-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch196_Segment000
-- name    : Polychromatic418967fa_Branch196_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:30:42.231215+00:00
-- url     : https://prove2.me/theorems/4c51bba9-fecb-47d0-8dd6-305a5cf7d555
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

def Polychromatic418967fa.branch_196_segment_000 : allB 133 196 :=
  allB_succ' 65 132 196 (Eq.refl Bool.true) (allA_succ_of_gcd 64 132 196 4 16 33 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 132 196
  (Polychromatic418967fa.accept_25_13_7_21_1_11411 63 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 132 196 2 31 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 132 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 61 132 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 132 196 4 15 33 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 132 196 (accept_3_3 59 132 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 196 2 29 66 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 132 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 132 196 4 14 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 132 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 132 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 132 196 2 27 66 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 132 196 (accept_3_3 53 132 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 196 4 13 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 196 (Polychromatic418967fa.accept_10_1_2_6_1_638
  51 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 132 196 2 25 66 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 196 4 12 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 196 (accept_3_3 47 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 196 2 23 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 132 196 (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 132 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 196 4 11 33 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 196
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 43 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 132 196 2 21 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 132 196 (accept_3_3 41 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 132 196 4 10 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 132 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 132 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 132 196 2 19 66 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 196
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 196 4 9 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 196 (accept_3_3 35 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  132 196 2 17 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 132 196 (Polychromatic418967fa.accept_17_16_13_9_1_11391 33 132 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 196 4 8 33 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 196 2 15 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 196 (accept_3_3 29 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 196 4 7 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 132 196 (Polychromatic418967fa.accept_17_10_13_9_1_3913 27 132 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 196 2 13 66 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 196
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 196 4 6 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 196 (accept_3_3 23 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  132 196 2 11 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 132 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 132 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 132 196 4 5 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 19
  132 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 196 2 9 66 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 196 (accept_3_3 17
  132 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 196 4 4 33 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 196
  (Polychromatic418967fa.accept_18_15_6_16_1_4730 15 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 196 2 7 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 132 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 196 4 3 33 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 196 (accept_3_3 11 132 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 196 2 5 66 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 196
  (Polychromatic418967fa.accept_13_9_2_1_1_813 9 132 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 196 4 2 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 196 (Polychromatic418967fa.accept_19_7_18_6_1_3095 7 132 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 196 2 3 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 196 (accept_3_3 5 132 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 196 4 1 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 132 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 132 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 196 2 1 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  132 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 131 196 (Eq.refl Bool.true)
  (allA_of_3_1 66 131 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 130 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 130 196 2 33 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 130 196 (accept_3_3 65 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 130 196 2 32 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 130 196 (Polychromatic418967fa.accept_25_13_5_21_1_9645 63 130 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 130 196 2 31 65 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 130 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 130 196 2 30 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 130 196 (accept_3_3 59 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 130 196 2 29 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 130 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 130 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 130 196 2 28 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 130 196
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 130 196 2 27 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 130 196 (accept_3_3 53 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 130 196 2 26 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 130 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 130 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 196 2 25 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 130 196 2 24 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 130 196 (accept_3_3 47 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 196 2 23 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 130 196 (Polychromatic418967fa.accept_19_7_16_6_1_4400 45 130 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 130 196 2 22 65 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 130 196 2 21 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 130 196 (accept_3_3 41 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 196 2 20 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 130 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 196 2 19 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 196
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 196 2 18 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 130 196 (accept_3_3 35 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 130 196 2 17 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 130 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 130 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 196 2 16 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 130 196 2 15 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 130 196 (accept_3_3 29 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 196 2 14 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 196 (Polychromatic418967fa.accept_19_8_16_6_1_5804 27 130 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 196 2 13 65 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 196 2 12 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 196 (accept_3_3 23 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 196 2 11 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 130 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 196 2 10 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 196
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 196 2 9 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 130 196 (accept_3_3 17 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  130 196 2 8 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 130 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 130 196 2 7 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 130 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 196 2 6 65 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 196 (accept_3_3 11 130 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 196 2 5 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 196
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 130 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 196 2 4 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 130 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 196 2 3 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 196 (accept_3_3 5 130 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 130 196 2 2 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 130 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 130 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 196 2 1 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 130
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 129 196 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 129 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 129 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 129 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 196 (accept_3_3 65 129 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 64
  129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 196
  (Polychromatic418967fa.accept_10_3_9_6_1_94 63 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 129 196 (accept_3_3 62 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 129 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 129 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 129 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 196 (accept_3_3 59 129 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 196
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 57 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 129 196 (accept_3_3 56 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 129 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 129 196 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 196 (accept_3_3 53 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 196 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 129
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 129 196 (accept_3_3 50 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 129 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 129 196 (Polychromatic418967fa.accept_19_10_15_6_1_5772 48 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 196 (accept_3_3 47 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 129 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 196
  (Polychromatic418967fa.accept_8_5_1_4_1_628 45 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 129 196 (accept_3_3 44 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 129 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 129 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 129 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 196 (accept_3_3 41 129 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 196
  (Polychromatic418967fa.accept_20_19_9_16_1_2744 39 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 196 (accept_3_3 38 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 129 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 196 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 129
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 196 (accept_3_3 35 129
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 196
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 34 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 129 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 129 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 196 (accept_3_3 32 129 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 129 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 129 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 196 (Polychromatic418967fa.accept_12_6_9_4_1_96
  30 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 196 (accept_3_3 29
  129 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 28 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 129 196 (Polychromatic418967fa.accept_20_7_9_16_1_11410 27 129 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 196 (accept_3_3 26 129 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 196 (accept_3_3 23 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 129 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 129 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 196 (accept_3_3 20 129 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 129 196 (accept_3_3 17 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 129 196 (Polychromatic418967fa.accept_17_16_10_9_1_11361 16 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 196 (accept_3_3 14 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 196
  (Polychromatic418967fa.accept_16_12_1_4_1_5403 12 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 129 196 (accept_3_3 11 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 129 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 129 196 (Polychromatic418967fa.accept_19_9_15_6_1_4396 9 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 196 (accept_3_3 8 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 129 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 129 196 (accept_3_3 5 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  129 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 129 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 129 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 129 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 196 (accept_3_3 2 129 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 128 196 (Eq.refl Bool.true)
  (allA_of_3_1 69 128 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 127 196 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 127 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 127 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 127 196 (accept_3_3 68 127 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 127 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 127 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 66
  127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 196 (accept_3_3 65
  127 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 196
  (Polychromatic418967fa.accept_18_10_1_16_1_579 64 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 127 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 127 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 127 196 (accept_3_3 62 127 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 127 196 (Polychromatic418967fa.accept_10_1_7_6_1_91 61 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 196 (Polychromatic418967fa.accept_9_6_1_7_1_577
  60 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 196 (accept_3_3 59
  127 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 58 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 127 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 127 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 196 (accept_3_3 56 127 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 127 196 (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 127 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 196
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 196 (accept_3_3 53 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 196 (Polychromatic418967fa.accept_17_1_8_9_1_1810 52 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 196 (accept_3_3 50 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 127 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 196 (accept_3_3 47 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 196 (accept_3_3 44 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 127 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 196 (accept_3_3 41 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 196 (accept_3_3 38 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 196 (Polychromatic418967fa.accept_13_11_10_1_1_1409 37 127 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 196
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 196 (accept_3_3 35 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 196 (accept_3_3 32 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 127 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 196 (accept_3_3 29 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 196 (Polychromatic418967fa.accept_16_12_15_4_1_5422 28 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 196 (accept_3_3 26 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 196 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 127 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 196 (accept_3_3 23 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 196 (accept_3_3 20 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 127 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 196
  (Polychromatic418967fa.accept_17_1_8_9_1_1810 18 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 196 (accept_3_3 17 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 196 (Polychromatic418967fa.accept_17_16_8_9_1_1772 16 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 196 (accept_3_3 14 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 127 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 196 (accept_3_3 11 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 196 (accept_3_3 8 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 196 (Polychromatic418967fa.accept_18_7_1_16_1_578 7 127 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 196 (accept_3_3 5 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 127 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 196 (accept_3_3 2 127 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 196 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 127 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 126 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 126 196 14 5 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 126 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 126 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 126 196 2 34 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 196 (Polychromatic418967fa.accept_13_2_9_1_1_67 67
  126 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 126 196 2 33 63 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 126 196 (accept_3_3 65
  126 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 196 2 32 63 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 126 196 7 9 18 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 126 196 2 31 63 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 196
  (Polychromatic418967fa.accept_19_4_12_6_1_11409 61 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 126 196 2 30 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 126 196 (accept_3_3 59 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 126 196 2 29 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 126 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 126 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 126 196 14 4 9 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 196
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 55 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 196 2 27 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 196 (accept_3_3 53 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 126 196 2 26 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 126 196 (Polychromatic418967fa.accept_11_7_5_9_1_884 51 126 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 126 196 2 25 63 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 126 196 7 7 18 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 126 196 2 24 63 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 126 196 (accept_3_3 47 126 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 196 2 23 63 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 196 2 22 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 196 (Polychromatic418967fa.accept_22_21_16_20_1_11408 43 126 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 196 14 3 9 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 196 (accept_3_3 41 126 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 196 2 20 63 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 196
  (Polychromatic418967fa.accept_12_3_6_4_1_400 39 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 196 2 19 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 196 (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 126 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 126 196 2 18 63 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 126 196 7 5 18 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 126 196 2 17 63 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 196 2 16 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 196 (Polychromatic418967fa.accept_13_5_9_1_1_1405 31 126 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 196 2 15 63 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 196 (accept_3_3 29 126 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 196 14 2 9 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 196
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 196 2 13 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 196 (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 126 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 126 196 2 12 63 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 126 196 (accept_3_3 23 126 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 196 2 11 63 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 196 7 3 18 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 196 2 10 63 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 196
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 196 2 9 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 196 (accept_3_3 17 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  126 196 2 8 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 126 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 126 196 14 1 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 126 196 (Polychromatic418967fa.accept_19_13_12_6_1_11362 13 126 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 196 2 6 63 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 196 (accept_3_3 11
  126 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 196 2 5 63 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 196 2 4 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 126 196 7 1 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 126 196 2 3 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 196 (accept_3_3 5 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126
  196 2 2 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  126 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 126 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 126 196 2 1 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 126 196 (Polychromatic418967fa.accept_16_1_14_4_1_3220 1 126 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 125 196 (Eq.refl Bool.true)
  (allA_of_3_1 72 125 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 124 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 124 196 4 18 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 196 (accept_3_3 71 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 196 2 35 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 196 (Polychromatic418967fa.accept_16_5_12_4_1_4325 69 124 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 196 4 17 31 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 196
  (Polychromatic418967fa.accept_16_3_12_4_1_170 67 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 196 2 33 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 196 (accept_3_3 65 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 196 4 16 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 196 (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 124 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 196 2 31 62 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 196
  (Polychromatic418967fa.accept_11_6_3_9_1_906 61 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 124 196 4 15 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 124 196 (accept_3_3 59 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 196 2 29 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 196 (Polychromatic418967fa.accept_15_12_4_1_1_3746 57 124 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 196 4 14 31 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 196
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 196 2 27 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 196 (accept_3_3 53 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 196 4 13 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 196 (Polychromatic418967fa.accept_16_3_12_4_1_170 51 124 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 196 2 25 62 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 196
  (Polychromatic418967fa.accept_16_1_12_4_1_695 49 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 196 4 12 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 196 (accept_3_3 47 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 196 2 23 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 124 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 196 4 11 31 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 196
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 43 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 124 196 2 21 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 124 196 (accept_3_3 41 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 196 4 10 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 196 (Polychromatic418967fa.accept_11_6_3_9_1_906 39 124 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 196 2 19 62 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 196
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 37 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 196 4 9 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 124 196 (accept_3_3 35 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  124 196 2 17 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 124 196 (Polychromatic418967fa.accept_15_3_4_1_1_1072 33 124 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 196 4 8 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 196
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 31 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 124 196 2 15 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 124 196 (accept_3_3 29 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 124 196 4 7 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 124 196 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 124 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 196 2 13 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 196 (Polychromatic418967fa.accept_10_5_4_6_1_319
  25 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 196 4 6 31 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 196
  (accept_3_3 23 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 196 2 11 62 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 196
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 124 196 4 5 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 124 196 (Polychromatic418967fa.accept_13_6_7_1_1_335 19 124 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 196 2 9 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 196 (accept_3_3 17 124 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 196 4 4 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 124 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 196 2 7 62 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 196
  (Polychromatic418967fa.accept_16_13_12_4_1_4323 13 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 124 196 4 3 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 124 196 (accept_3_3 11 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 124 196 2 5 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 124 196 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 124 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 196 4 2 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 196 (Polychromatic418967fa.accept_16_7_12_4_1_1347 7 124 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 196 2 3 62 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 196 (accept_3_3 5 124 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 196 4 1 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 124 196 (Polychromatic418967fa.accept_13_3_7_1_1_334 3
  124 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 196 2 1 62 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 196
  (Polychromatic418967fa.accept_16_1_12_4_1_695 1 124 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 124 196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 123 196
  (Eq.refl Bool.true) (allA_succ_of_accept 73 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 196
  (Polychromatic418967fa.accept_13_7_6_1_1_368 72 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 123 196 (accept_3_3 71 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 123 196 (Polychromatic418967fa.accept_11_4_2_9_1_496 70 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 123 196 (Polychromatic418967fa.accept_10_9_3_6_1_686 69 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 123 196 (accept_3_3 68 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 123 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 123 196 (accept_3_3 65 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 123 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 123 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 196 (accept_3_3 62 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 196
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 60 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 123 196 (accept_3_3 59 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 123 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 123 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 196 (accept_3_3 56 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 123 196 (accept_3_3 53 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 123 196 (Polychromatic418967fa.accept_19_14_9_6_1_8633 52 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 123 196 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 196 (accept_3_3 50 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 123 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 123 196 (accept_3_3 47 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 123 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 123 196 (Polychromatic418967fa.accept_18_9_15_16_1_8759 45 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 196 (accept_3_3 44 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 123 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 123 196 (accept_3_3 41 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 123 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 123 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 196 (accept_3_3 38 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 196
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 123 196 (accept_3_3 35 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 123 196 (Polychromatic418967fa.accept_13_8_6_1_1_3808 34 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 123 196 (Polychromatic418967fa.accept_13_7_6_1_1_368 33 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 196 (accept_3_3 32 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 123 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 123 196 (accept_3_3 29 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 123 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 123 196 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 196 (accept_3_3 26 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 123 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 196
  (Polychromatic418967fa.accept_16_8_11_4_1_3290 24 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 123 196 (accept_3_3 23 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 123 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 123 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 196 (accept_3_3 20 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 196
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 196 (accept_3_3 17 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 196 (Polychromatic418967fa.accept_13_3_6_1_1_3797 16 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 196 (accept_3_3 14 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 196 (accept_3_3 11 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 196 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 196 (accept_3_3 8 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 196 (accept_3_3 5 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 123 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 196 (accept_3_3 2 123 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 123 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 122 196 (Eq.refl
  Bool.true) (allA_of_3_1 75 122 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 121 196 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 121 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 121 196 (accept_3_3 74 121 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 121 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 121 196 (Polychromatic418967fa.accept_10_2_1_6_1_634
  72 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 196 (accept_3_3 71
  121 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 196
  (Polychromatic418967fa.accept_12_10_1_4_1_392 70 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 121 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 121 196 (accept_3_3 68 121 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 121 196 (Polychromatic418967fa.accept_10_7_1_6_1_673 67 121 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 121 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 121 196 (accept_3_3 65 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 121 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 196 (accept_3_3 62 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 121 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 121 196 (accept_3_3 59 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 121 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 196 (accept_3_3 56 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 121 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 121 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 121 196
  (Polychromatic418967fa.accept_19_16_7_6_1_7201 54 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 121 196 (accept_3_3 53 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 121 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 196 (accept_3_3 50 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 121 196 (Polychromatic418967fa.accept_13_10_4_1_1_2142 49 121 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 121 196 (accept_3_3 47 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 121 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 196 (accept_3_3 44 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 196 (Polychromatic418967fa.accept_16_11_9_4_1_5438 43 121 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 121 196 (accept_3_3 41 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 121 196 (Polychromatic418967fa.accept_16_8_9_4_1_630 40 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 196 (accept_3_3 38 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 121 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 196
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 121 196 (accept_3_3 35 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 121 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 196 (accept_3_3 32 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 196 (Polychromatic418967fa.accept_13_5_4_1_1_364 31 121 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 121 196 (accept_3_3 29 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 121 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 196 (accept_3_3 26 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 196 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 121 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 196 (accept_3_3 23 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 196 (accept_3_3 20 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 121 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 196
  (Polychromatic418967fa.accept_13_5_4_1_1_364 18 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 196 (accept_3_3 17 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 196 (Polychromatic418967fa.accept_13_3_4_1_1_363 16 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 196 (accept_3_3 14 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 121 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 196 (accept_3_3 11 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 196 (accept_3_3 8 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 196 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 121 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 196 (accept_3_3 5 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 196 (Polychromatic418967fa.accept_17_4_2_9_1_3896 4 121 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 196 (accept_3_3 2 121 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 121 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 120 196 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 120 196 4 19 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 120 196 (Polychromatic418967fa.accept_16_11_8_4_1_2234 75 120 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 120 196 2 37 60 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 120 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 196 4 18 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 120 196 (accept_3_3 71 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 120 196 2 35 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 120 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 120 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 120 196 4 17 30 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 196 2 33 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 196 (accept_3_3 65 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 120 196 4 16 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 120 196 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 120 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 120 196 2 31 60 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 196
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 61 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 196 4 15 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 196 (accept_3_3 59 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 120 196 2 29 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 120 196 (Polychromatic418967fa.accept_13_5_3_1_1_1398 57 120 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 120 196 4 14 30 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 120 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 196 2 27 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 196 (accept_3_3 53 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 120 196 4 13 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 120 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 120 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 196 2 25 60 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 196 4 12 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 196 (accept_3_3 47 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 120 196 2 23 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 120 196 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 120 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 120 196 4 11 30 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 196
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 43 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 196 2 21 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 196 (accept_3_3 41 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 196 4 10 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 120 196 (Polychromatic418967fa.accept_16_7_8_4_1_689 39 120 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 196 2 19 60 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 196 4 9 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 120 196 (accept_3_3 35 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  120 196 2 17 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 120 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 120 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 196 4 8 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 31
  120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 196 2 15 60 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 196 (accept_3_3 29
  120 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 196 4 7 30 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 196
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 120 196 2 13 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 120 196 (Polychromatic418967fa.accept_16_9_8_4_1_1354 25 120 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 196 4 6 30 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 196 (accept_3_3 23 120 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 196 2 11 60 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 196
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 21 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 196 4 5 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 120 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 196 2 9 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 196 (accept_3_3 17 120 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 196 4 4 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 120 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 120 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 196 2 7 60 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 120 196 4 3 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 120 196 (accept_3_3 11 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  120 196 2 5 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 120 196 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 120 196 4 2 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 120 196 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 120 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 196 2 3 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 196 (accept_3_3 5 120 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 196 4 1 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 120 196 (Polychromatic418967fa.accept_16_3_8_4_1_3279 3 120 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 196 2 1 60 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 119 196
  (Eq.refl Bool.true) (allA_of_3_1 78 119 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 118 196 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 118 196 2 39 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 118 196 (accept_3_3 77 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 118 196 2 38 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 118 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 118 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 118 196 2 37 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 118 196
  (Polychromatic418967fa.accept_10_3_8_6_1_326 73 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 118 196 2 36 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 118 196 (accept_3_3 71 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 118 196 2 35 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 118 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 118 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 118 196 2 34 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 118 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 118 196 2 33 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 118 196 (accept_3_3 65 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 118 196 2 32 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 118 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 118 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 196 2 31 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 118 196 2 30 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 118 196 (accept_3_3 59 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 196 2 29 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 118 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 196 2 28 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 118 196 2 27 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 118 196 (accept_3_3 53 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 196 2 26 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 118 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 196 2 25 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 196 2 24 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 196 (accept_3_3 47 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 196 2 23 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 196 (Polychromatic418967fa.accept_16_13_6_4_1_3277 45 118 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 196 2 22 59 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 196
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 196 2 21 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 196 (accept_3_3 41 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 196 2 20 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 118 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 196 2 19 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 196 2 18 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 196 (accept_3_3 35 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 196 2 17 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 118 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 196 2 16 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 196 2 15 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 196 (accept_3_3 29 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 196 2 14 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 196 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 118 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 196 2 13 59 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 196 2 12 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 196 (accept_3_3 23 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 196 2 11 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 118 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 196 2 10 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 196 2 9 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 196 (accept_3_3 17 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 196 2 8 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 196 2 7 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 118 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 196 2 6 59 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 196 (accept_3_3 11 118 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 196 2 5 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 196
  (Polychromatic418967fa.accept_21_9_13_7_1_5154 9 118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 196 2 4 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 118 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 196 2 3 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 196 (accept_3_3 5 118 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 196 2 2 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 118 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 196 2 1 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  118 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 117 196 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 196 (Polychromatic418967fa.accept_12_6_9_4_1_96
  78 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 196 (accept_3_3 77
  117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 196
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 76 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 117 196 (Polychromatic418967fa.accept_17_7_15_9_1_9019 75 117 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 196 (accept_3_3 74 117 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 196 (Polychromatic418967fa.accept_16_8_5_4_1_674
  72 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 196 (accept_3_3 71
  117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 196
  (Polychromatic418967fa.accept_16_6_5_4_1_4330 70 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 117 196 (Polychromatic418967fa.accept_17_1_15_9_1_1743 69 117 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 196 (accept_3_3 68 117 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 196 (Polychromatic418967fa.accept_12_6_9_4_1_96
  66 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 196 (accept_3_3 65
  117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 196
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 64 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 117 196 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 117 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 196 (accept_3_3 62 117 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 196 (Polychromatic418967fa.accept_11_5_7_9_1_2696
  60 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 196 (accept_3_3 59
  117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 196
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 58 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 117 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 196 (accept_3_3 56 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 117 196 (accept_3_3 53 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 117 196 (Polychromatic418967fa.accept_17_1_15_9_1_1743 52 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 117 196 (Polychromatic418967fa.accept_10_1_7_6_1_91 51 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 196 (accept_3_3 50 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 196
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 196 (accept_3_3 47 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 196 (Polychromatic418967fa.accept_11_2_7_9_1_890 46 117 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 196 (Polychromatic418967fa.accept_19_7_3_6_1_8663 45 117
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 196 (accept_3_3 44 117
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 196 (accept_3_3 41 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 196 (Polychromatic418967fa.accept_16_8_5_4_1_674 40 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 117 196 (Polychromatic418967fa.accept_19_1_3_6_1_5827 39 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 196 (accept_3_3 38 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 117 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 196
  (Polychromatic418967fa.accept_19_17_3_6_1_8662 36 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 117 196 (accept_3_3 35 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 117 196 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 117 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 196 (accept_3_3 32 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 117 196 (accept_3_3 29 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 117 196 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 196 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 196 (accept_3_3 26 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 117 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 196
  (Polychromatic418967fa.accept_11_2_7_9_1_890 24 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 196 (accept_3_3 23 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 117 196 (Polychromatic418967fa.accept_16_6_5_4_1_4330 22 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 196 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 196 (accept_3_3 20 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 196 (accept_3_3 17 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 196 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 196 (Polychromatic418967fa.accept_16_15_5_4_1_6678 15 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 196 (accept_3_3 14 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 196
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 12 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 196 (accept_3_3 11 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 117 196 (Polychromatic418967fa.accept_23_10_2_12_1_11407 10 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 196 (accept_3_3 8 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 117 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 196 (accept_3_3 5 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 196 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 117 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 196 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 196 (accept_3_3 2 117 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 116 196 (Eq.refl
  Bool.true) (allA_of_3_1 81 116 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 115 196 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 115 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 115 196 (accept_3_3 80 115 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 115 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 79 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 115 196
  (Polychromatic418967fa.accept_17_10_13_9_1_3913 78 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 115 196 (accept_3_3 77 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 115 196 (Polychromatic418967fa.accept_16_12_3_4_1_4317 76 115 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 115 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 115 196 (accept_3_3 74 115 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 196 (Polychromatic418967fa.accept_11_7_5_9_1_884
  73 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 196
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 72 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 115 196 (accept_3_3 71 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 115 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 196 (accept_3_3 68 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 115 196 (Polychromatic418967fa.accept_15_7_10_1_1_1836 67 115 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 196
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 66 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 115 196 (accept_3_3 65 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 115 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 64 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 196 (accept_3_3 62 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 196 (Polychromatic418967fa.accept_10_1_5_6_1_649 61 115 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 196
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 60 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 115 196 (accept_3_3 59 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 115 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 196 (accept_3_3 56 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 115 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 115 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 196
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 196 (accept_3_3 53 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 196 (Polychromatic418967fa.accept_15_7_10_1_1_1836 52 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 196 (accept_3_3 50 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 196 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 115 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 196
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 48 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 196 (accept_3_3 47 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 115 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 196 (accept_3_3 44 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 196 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 115 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 196
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 42 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 196 (accept_3_3 41 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 115 196 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 196 (accept_3_3 38 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 196 (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 115 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 196
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 115 196 (accept_3_3 35 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 115 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 115 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 115 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 196 (accept_3_3 32 115 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 196 (Polychromatic418967fa.accept_8_7_3_4_1_404
  31 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 196
  (Polychromatic418967fa.accept_19_11_1_6_1_5752 30 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 196 (accept_3_3 29 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 196 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 196 (accept_3_3 26 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 196 (Polychromatic418967fa.accept_13_12_11_1_1_2920 25 115 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 196
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 196 (accept_3_3 23 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 196 (accept_3_3 20 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 196 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 115 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 196
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 196 (accept_3_3 17 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 196 (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 196 (accept_3_3 14 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 196 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 115 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 196
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 115 196 (accept_3_3 11 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 115 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 115 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 115 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 196 (accept_3_3 8 115 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 7
  115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 196
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 6 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 196 (accept_3_3 5 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 115 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 196 (accept_3_3 2 115 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 196 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 115 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 114 196 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 114 196 2 41 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 114 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 114 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 114 196 2 40 57 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 114 196
  (Polychromatic418967fa.accept_11_2_4_9_1_484 79 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 196 2 39 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 196 (accept_3_3 77 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 114 196 2 38 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 114 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 114 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 114 196 2 37 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 196
  (Polychromatic418967fa.accept_9_1_6_7_1_285 73 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 196 2 36 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 196 (accept_3_3 71 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 114 196 2 35 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 114 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 114 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 114 196 2 34 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 67 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 196 2 33 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 196 (accept_3_3 65 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 114 196 2 32 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 114 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 114 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 114 196 2 31 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 196
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 61 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 196 2 30 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 196 (accept_3_3 59 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 114 196 2 29 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 114 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 114 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 114 196 2 28 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 196
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 196 2 27 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 196 (accept_3_3 53 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 114 196 2 26 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 114 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 114 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 114 196 2 25 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 196 2 24 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 196 (accept_3_3 47 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 114 196 2 23 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 114 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 114 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 114 196 2 22 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 196
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 43 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 196 2 21 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 196 (accept_3_3 41 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 114 196 2 20 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 114 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 114 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 114 196 2 19 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 196
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 196 2 18 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 196 (accept_3_3 35 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 196 2 17 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 114 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 114 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 114 196 2 16 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 196 2 15 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 196 (accept_3_3 29 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 196 2 14 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 114 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 196 2 13 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 196
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 196 2 12 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 196 (accept_3_3 23 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 196 2 11 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 114 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 196 2 10 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 196
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 196 2 9 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 196 (accept_3_3 17 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  114 196 2 8 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 114 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 114 196 2 7 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 114 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 114 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 196 2 6 57 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 196 (accept_3_3 11 114 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 196 2 5 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 196 2 4 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 196 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 114 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 196 2 3 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 196 (accept_3_3 5 114 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 196 2 2 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 114 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 114 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 196 2 1 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  114 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 113 196 (Eq.refl
  Bool.true) (allA_of_3_1 84 113 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 85 112 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 112 196 28 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 112 196 (accept_3_3 83 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82
  112 196 2 41 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 81 112 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 112 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 112 196 4 20 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 112 196 (Polychromatic418967fa.accept_18_7_4_16_1_2299
  79 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 112 196 2 39 56 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 112 196 7 11 16
  28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 112 196 4 19
  28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 112 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 75 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 112 196 2 37 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 112 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 112 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 112 196 4 18 28 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 112 196 (accept_3_3 71 112 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 112 196 14 5 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 112 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 69
  112 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 112 196 4 17 28 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 112 196
  (Polychromatic418967fa.accept_17_16_10_9_1_11361 67 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 112 196 2 33 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 112 196 (accept_3_3 65 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 112 196 4 16 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 112 196 7 9 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 62 112 196 2 31 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 112 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 61 112 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 112 196 4 15 28 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 112 196 (accept_3_3 59 112 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 112 196 2 29 56 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 112 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 112 196 28 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 112 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 112 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 112 196 2 27 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 112 196 (accept_3_3 53 112 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 112 196 4 13 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 112 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 112 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 196 2 25 56 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 112 196 7 7 16 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 112 196 4 12 28 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 112 196
  (accept_3_3 47 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 112 196 2 23 56 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 112 196
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 112 196 4 11 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 112 196 (Polychromatic418967fa.accept_18_7_4_16_1_2299 43 112 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 112 196 14 3 8 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 112 196 (accept_3_3 41 112 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 112 196 4 10 28 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 112 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 112 196 2 19 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 112 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 112 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 112 196 4 9 28 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 112 196 7 5 16 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 112 196 2 17 56 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 112 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 112 196 4 8 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 112 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 112 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 196 2 15 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 196 (accept_3_3 29 112 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 196 28 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 112 196 (Polychromatic418967fa.accept_19_8_17_6_1_5728 27 112 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 196 2 13 56 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 196
  (Polychromatic418967fa.accept_13_12_8_1_1_825 25 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 196 4 6 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 112 196 (accept_3_3 23 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  112 196 2 11 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  21 112 196 7 3 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  20 112 196 4 5 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 112 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 112 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 112 196 2 9 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 112 196 (accept_3_3 17 112 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 112 196 4 4 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 112 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 112 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 112 196 14 1 8 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 112 196
  (Polychromatic418967fa.accept_17_13_10_9_1_946 13 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 112 196 4 3 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 112 196 (accept_3_3 11 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  112 196 2 5 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 112 196 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 112 196 4 2 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 7 112 196 7 1 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 112 196 2 3 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 112 196 (accept_3_3 5 112 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 112 196 4 1 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 112 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 112 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 196 2 1 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 111 196
  (Eq.refl Bool.true) (allA_succ_of_accept 85 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 196
  (Polychromatic418967fa.accept_13_6_7_1_1_335 84 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 111 196 (accept_3_3 83 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 111 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 111 196 (Polychromatic418967fa.accept_13_3_7_1_1_334 81 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 196 (accept_3_3 80 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 111 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 78 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 196 (accept_3_3 77 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 111 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 196 (accept_3_3 74 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 196
  (Polychromatic418967fa.accept_10_2_1_6_1_634 72 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 111 196 (accept_3_3 71 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 111 196 (Polychromatic418967fa.accept_15_10_6_1_1_3707 70 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 111 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 196 (accept_3_3 68 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 196 (accept_3_3 65 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 111 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 196 (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 196 (accept_3_3 62 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 111 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 111 196 (accept_3_3 59 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 111 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 111 196 (Polychromatic418967fa.accept_10_7_1_6_1_673 57 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 196 (accept_3_3 56 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 111 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 196
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 196 (accept_3_3 53 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 111 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 196 (accept_3_3 50 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 196
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 196 (accept_3_3 47 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 196 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 196 (accept_3_3 44 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 111 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 196 (accept_3_3 41 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 196 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 196 (accept_3_3 38 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 111 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 196
  (Polychromatic418967fa.accept_22_14_1_20_1_11406 36 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 196 (accept_3_3 35 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 196 (Polychromatic418967fa.accept_13_8_7_1_1_1385 34 111 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 111 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 196 (accept_3_3 32 111 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 196 (accept_3_3 29 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 196 (accept_3_3 26 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 196 (accept_3_3 23 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 196 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 196 (accept_3_3 20 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 196 (accept_3_3 17 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 196 (Polychromatic418967fa.accept_13_3_7_1_1_334 16 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 196 (accept_3_3 14 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 196
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 196 (accept_3_3 11 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 196 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 196 (accept_3_3 8 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 196 (accept_3_3 5 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 111 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 196 (accept_3_3 2 111 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 111 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 110 196
  (Eq.refl Bool.true) (allA_of_3_1 87 110 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 109 196 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 109 196 (accept_3_3 86 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 109 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 109 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 84 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 109 196 (accept_3_3 83 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 109 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 109 196 (accept_3_3 80 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 109 196 (Polychromatic418967fa.accept_18_7_1_16_1_578 79 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 109 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 78 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 109 196 (accept_3_3 77 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 109 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 109 196 (accept_3_3 74 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 109 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 73 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 109 196
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 72 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 109 196 (accept_3_3 71 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 109 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 196 (accept_3_3 68 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 109 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 109 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 109 196 (accept_3_3 65 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 109 196 (Polychromatic418967fa.accept_13_12_5_1_1_1383 64 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 196 (accept_3_3 62 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 109 196 (Polychromatic418967fa.accept_13_9_5_1_1_1382 61 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 109 196 (accept_3_3 59 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 109 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 196 (accept_3_3 56 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 196 (Polychromatic418967fa.accept_10_5_9_6_1_697 55 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 196
  (Polychromatic418967fa.accept_16_6_13_4_1_643 54 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 196 (accept_3_3 53 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 196 (Polychromatic418967fa.accept_11_8_10_9_1_1401 52 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 196 (accept_3_3 50 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 196 (accept_3_3 47 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 196 (accept_3_3 44 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 43 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 196 (accept_3_3 41 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 196 (accept_3_3 38 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 196 (Polychromatic418967fa.accept_21_16_4_7_1_5191 37 109 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 196
  (Polychromatic418967fa.accept_17_2_7_9_1_2796 36 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 196 (accept_3_3 35 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 196 (Polychromatic418967fa.accept_11_1_10_9_1_871 34 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 196 (accept_3_3 32 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 196 (accept_3_3 29 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 196 (Polychromatic418967fa.accept_16_12_13_4_1_3198 28 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 196 (accept_3_3 26 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 196 (accept_3_3 23 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 196 (accept_3_3 20 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 196 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 109 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 196
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 196 (accept_3_3 17 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 196 (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 196 (accept_3_3 14 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 196 (accept_3_3 11 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 196 (accept_3_3 8 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 196 (Polychromatic418967fa.accept_16_7_13_4_1_1348 7 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 196 (accept_3_3 5 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 109 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 196 (accept_3_3 2 109 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 109 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 108 196
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 108 196 4 22 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 108 196 (Polychromatic418967fa.accept_16_7_12_4_1_1347 87 108
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 108 196 2 43 54 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 196
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 85 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 196 4 21 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 196 (accept_3_3 83 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 108 196 2 41 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 108 196 (Polychromatic418967fa.accept_13_3_4_1_1_363 81 108 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 108 196 4 20 27 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 196
  (Polychromatic418967fa.accept_15_4_3_1_1_487 79 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 196 2 39 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 196 (accept_3_3 77 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 108 196 4 19 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 108 196 (Polychromatic418967fa.accept_13_10_4_1_1_2142 75 108 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 108 196 2 37 54 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 196
  (Polychromatic418967fa.accept_10_3_8_6_1_326 73 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 196 4 18 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 196 (accept_3_3 71 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 108 196 2 35 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 108 196 (Polychromatic418967fa.accept_16_5_12_4_1_4325 69 108 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 108 196 4 17 27 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 196
  (Polychromatic418967fa.accept_16_3_12_4_1_170 67 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 196 2 33 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 196 (accept_3_3 65 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 108 196 4 16 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 108 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 108 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 108 196 2 31 54 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 196
  (Polychromatic418967fa.accept_16_13_12_4_1_4323 61 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 108 196 4 15 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 108 196 (accept_3_3 59 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 108 196 2 29 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 108 196 (Polychromatic418967fa.accept_13_5_4_1_1_364 57 108 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 108 196 4 14 27 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 196
  (Polychromatic418967fa.accept_13_3_4_1_1_363 55 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 196 2 27 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 196 (accept_3_3 53 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 108 196 4 13 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 108 196 (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 108 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 196 2 25 54 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 196
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 49 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 196 4 12 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 196 (accept_3_3 47 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 108 196 2 23 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 196 (Polychromatic418967fa.accept_16_13_12_4_1_4323 45 108 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 196 4 11 27 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 196
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 196 2 21 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 196 (accept_3_3 41 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 196 4 10 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 196 (Polychromatic418967fa.accept_16_7_12_4_1_1347 39 108 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 196 2 19 54 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 196
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 37 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 196 4 9 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 196 (accept_3_3 35 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  108 196 2 17 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 108 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 108 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 196 4 8 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 196 (Polychromatic418967fa.accept_13_5_4_1_1_364
  31 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 196 2 15 54 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 196
  (accept_3_3 29 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 196 4 7 27 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 196
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 27 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 108 196 2 13 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 108 196 (Polychromatic418967fa.accept_16_9_12_4_1_3255 25 108 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 196 4 6 27 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 196 (accept_3_3 23 108 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 196 2 11 54 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 196
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 196 4 5 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 108 196 (Polychromatic418967fa.accept_15_4_3_1_1_487 19 108 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 196 2 9 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 196 (accept_3_3 17 108 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 196 4 4 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 196 (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 108
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 196 2 7 54 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 196
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 196 4 3 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 196 (accept_3_3 11 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  108 196 2 5 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 108 196 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 108 196 4 2 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 108 196 (Polychromatic418967fa.accept_16_7_12_4_1_1347 7 108 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 196 2 3 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 196 (accept_3_3 5 108 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 196 4 1 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 108 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 108 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 196 2 1 54 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 196
  (Polychromatic418967fa.accept_16_1_12_4_1_695 1 108 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  90 107 196 (Eq.refl Bool.true) (allA_of_3_1 90 107 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 106 196
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 106 196 2 45 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 106 196 (accept_3_3 89 106 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 106 196 2 44 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 106 196 (Polychromatic418967fa.accept_13_9_2_1_1_813 87 106 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 106 196 2 43 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 106 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 106 196 2 42 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 106 196 (accept_3_3 83 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 106 196 2 41 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 106 196 (Polychromatic418967fa.accept_13_3_2_1_1_2907 81 106 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 106 196 2 40 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 106 196
  (Polychromatic418967fa.accept_11_2_7_9_1_890 79 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 106 196 2 39 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 106 196 (accept_3_3 77 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 106 196 2 38 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 106 196 (Polychromatic418967fa.accept_19_18_11_6_1_5768 75 106 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 196 2 37 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 196 2 36 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 196 (accept_3_3 71 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 196 2 35 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 196 (Polychromatic418967fa.accept_21_6_1_7_1_11405 69 106 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 196 2 34 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 106 196 2 33 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 196 (accept_3_3 65 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 196 2 32 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 196 (Polychromatic418967fa.accept_17_12_4_9_1_3889 63 106 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 196 2 31 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 196 2 30 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 196 (accept_3_3 59 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 196 2 29 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 196 (Polychromatic418967fa.accept_11_2_7_9_1_890 57 106 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 196 2 28 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 196 2 27 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 196 (accept_3_3 53 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 196 2 26 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 196 (Polychromatic418967fa.accept_13_12_2_1_1_2909 51 106 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 196 2 25 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 196
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 196 2 24 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 196 (accept_3_3 47 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 196 2 23 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 196 (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 106 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 196 2 22 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 196 2 21 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 196 (accept_3_3 41 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 196 2 20 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 196 (Polychromatic418967fa.accept_19_1_11_6_1_7152 39 106 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 196 2 19 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 196 2 18 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 196 (accept_3_3 35 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 196 2 17 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 196 (Polychromatic418967fa.accept_19_14_11_6_1_7151 33 106 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 196 2 16 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 196 2 15 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 196 (accept_3_3 29 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 196 2 14 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 196 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 106 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 196 2 13 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 196 2 12 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 196 (accept_3_3 23 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 196 2 11 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 196 (Polychromatic418967fa.accept_20_1_6_16_1_6991 21 106 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 196 2 10 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 196 2 9 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 196 (accept_3_3 17 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 196 2 8 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 196 (Polychromatic418967fa.accept_19_15_11_6_1_11404 15 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 196 2 7 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 196 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 106 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 196 2 6 53 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 196 (accept_3_3 11
  106 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 196 2 5 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 196
  (Polychromatic418967fa.accept_13_9_2_1_1_813 9 106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 196 2 4 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 106 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 196 2 3 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 196 (accept_3_3 5 106 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 196 2 2 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 196 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 106 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 196 2 1 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  106 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 105 196
  (Eq.refl Bool.true) (allA_succ_of_gcd 91 105 196 7 13 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 105 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 90 105 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 196 (accept_3_3 89 105 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 196 (Polychromatic418967fa.accept_16_8_9_4_1_630
  88 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 105 196
  (Polychromatic418967fa.accept_23_18_13_12_1_9761 87 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 196 (accept_3_3 86 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 105 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 105 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 105 196 7 12 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 105 196 (accept_3_3 83 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 105 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 105 196
  (Polychromatic418967fa.accept_10_1_5_6_1_649 81 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 105 196 (accept_3_3 80 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 105 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 105 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 78 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 105 196 7 11 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 105 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 76 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 105 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 105 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 196 (accept_3_3 74 105 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 105 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 196 (Polychromatic418967fa.accept_16_8_9_4_1_630
  72 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 196 (accept_3_3 71
  105 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 196 7 10 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 105 196
  (Polychromatic418967fa.accept_8_5_1_4_1_628 69 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 105 196 (accept_3_3 68 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 105 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 105 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 196 (accept_3_3 65 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 105 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 105 196 7 9 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 105 196 (accept_3_3 62 105 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 61
  105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 196
  (Polychromatic418967fa.accept_16_12_9_4_1_4345 60 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 105 196 (accept_3_3 59 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 105 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 105 196 7 8 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 105 196
  (Polychromatic418967fa.accept_6_1_3_4_1_1 55 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 105 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 105 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 196 (accept_3_3 53 105 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 105 196 (Polychromatic418967fa.accept_17_1_3_9_1_958 52 105 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 196
  (Polychromatic418967fa.accept_10_1_5_6_1_649 51 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 105 196 (accept_3_3 50 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49
  105 196 7 7 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  48 105 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 105 196 (accept_3_3 47 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 105 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 105 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 196 (accept_3_3 44 105 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43
  105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 196 7 6 15 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 196 (accept_3_3 41
  105 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 40 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 105 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 105 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 196 (accept_3_3 38 105 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 105 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 196 (Polychromatic418967fa.accept_11_3_6_9_1_1378
  36 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 196 7 5 15 28
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 196
  (Polychromatic418967fa.accept_10_4_5_6_1_651 34 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 105 196 (Polychromatic418967fa.accept_19_14_10_6_1_4372 33 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 196 (accept_3_3 32 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 105 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 196 (accept_3_3 29 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28
  105 196 7 4 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 105 196 (Polychromatic418967fa.accept_16_11_9_4_1_5438 27 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 196 (accept_3_3 26 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 105 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 105
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 196 (accept_3_3 23 105
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 22 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 105 196 7 3 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 105 196 (accept_3_3 20 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 105 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 105 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 196 (accept_3_3 17 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 196 (Polychromatic418967fa.accept_19_16_10_6_1_11403 16 105 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 196
  (Polychromatic418967fa.accept_19_15_10_6_1_7169 15 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 105 196 7 2 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 105 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 196 (accept_3_3 11 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 196 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 196 (accept_3_3 8 105 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 105 196 7 1 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 105 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 105 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 196 (accept_3_3 5 105 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 105 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 196 (accept_3_3 2 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 104 196
  (Eq.refl Bool.true) (allA_of_3_1 93 104 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 103 196 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 103 196 (accept_3_3 92 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 103 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 91 103 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 103 196
  (Polychromatic418967fa.accept_11_2_4_9_1_484 90 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 103 196 (accept_3_3 89 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 103 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 88 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 103 196 (accept_3_3 86 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 103 196 (Polychromatic418967fa.accept_15_10_13_1_1_3698 85 103 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 103 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 103 196 (accept_3_3 83 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 103 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 103 196 (accept_3_3 80 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 103 196 (Polychromatic418967fa.accept_10_9_3_6_1_686 79 103 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 103 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 103 196 (accept_3_3 77 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 103 196 (Polychromatic418967fa.accept_13_11_12_1_1_2154 76 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 103 196 (accept_3_3 74 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 103 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 103 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 103 196
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 72 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 103 196 (accept_3_3 71 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 103 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 103 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 103 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 196 (accept_3_3 68 103 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 103 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 67
  103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 103 196 (accept_3_3 65 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 103 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 196 (accept_3_3 62 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 196 (Polychromatic418967fa.accept_16_13_7_4_1_3248 61 103 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 103 196 (accept_3_3 59 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 103 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 196 (accept_3_3 56 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 103 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 196
  (Polychromatic418967fa.accept_13_2_12_1_1_343 54 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 103 196 (accept_3_3 53 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 103 196 (Polychromatic418967fa.accept_19_14_8_6_1_981 52 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 196 (accept_3_3 50 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 196 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 103 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 196 (accept_3_3 47 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 196 (accept_3_3 44 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 103 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 196 (accept_3_3 41 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 196 (Polychromatic418967fa.accept_15_10_13_1_1_3698 40 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 196 (accept_3_3 38 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 103 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 196
  (Polychromatic418967fa.accept_19_17_8_6_1_7146 36 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 196 (accept_3_3 35 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 196 (accept_3_3 32 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 196 (Polychromatic418967fa.accept_13_5_12_1_1_2123 31 103 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 196 (accept_3_3 29 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 196 (accept_3_3 26 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 196 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 103 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 196 (accept_3_3 23 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 196 (accept_3_3 20 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 103 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 196
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 196 (accept_3_3 17 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 196 (Polychromatic418967fa.accept_19_16_8_6_1_4407 16 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 196 (accept_3_3 14 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 196 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 103 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 196 (accept_3_3 11 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 196 (accept_3_3 8 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 196 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 103 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 196 (accept_3_3 5 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 196 (Polychromatic418967fa.accept_21_4_19_7_1_5142 4 103 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 196 (accept_3_3 2 103 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 103 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 102
  196 (Eq.refl Bool.true) (allA_succ_of_gcd 94 102 196 2 47 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 102 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 93 102 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 196 2 46 51 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 91 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 196 2 45 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 196 (accept_3_3 89 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 102 196 2 44 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 102 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 102 196 2 43 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 85 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 196 2 42 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 196 (accept_3_3 83 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 102 196 2 41 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 102 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 102 196 2 40 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 196
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 79 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 196 2 39 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 196 (accept_3_3 77 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 102 196 2 38 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 102 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 75 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 102 196 2 37 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 196 2 36 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 196 (accept_3_3 71 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 102 196 2 35 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 102 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 102 196 2 34 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 196 2 33 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 196 (accept_3_3 65 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 102 196 2 32 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 102 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 102 196 2 31 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 196
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 196 2 30 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 196 (accept_3_3 59 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 102 196 2 29 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 102 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 196 2 28 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 196 2 27 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 196 (accept_3_3 53 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 196 2 26 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 102 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 196 2 25 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 196 2 24 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 196 (accept_3_3 47 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 196 2 23 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 196 2 22 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 196
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 43 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 102 196 2 21 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 102 196 (accept_3_3 41 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 102 196 2 20 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 196 (Polychromatic418967fa.accept_11_6_3_9_1_906 39 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 196 2 19 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 196 2 18 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 196 (accept_3_3 35 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 196 2 17 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 196 2 16 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 196 2 15 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 196 (accept_3_3 29 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 196 2 14 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 196 2 13 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 196
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 25 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 102 196 2 12 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 102 196 (accept_3_3 23 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 196 2 11 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 196 2 10 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 196 2 9 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 196 (accept_3_3 17 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  102 196 2 8 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 102 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 102 196 2 7 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 102 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 102 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 196 2 6 51 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 196 (accept_3_3 11 102 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 196 2 5 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 102 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 196 2 4 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 196 (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 102 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 196 2 3 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 196 (accept_3_3 5 102 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 196 2 2 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 102 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 196 2 1 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 102
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 101
  196 (Eq.refl Bool.true) (allA_of_3_1 96 101 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 100 196
  (Eq.refl Bool.true) (allA_succ_of_gcd 96 100 196 4 24 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 100 196 (accept_3_3 95 100 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 94 100 196 2 47 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 93 100 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 93 100 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 100 196 4 23 25 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 100 196
  (Polychromatic418967fa.accept_17_6_15_9_1_1791 91 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 100 196 2 45 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 100 196 (accept_3_3 89 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 100 196 4 22 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 100 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 87 100 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 100 196 2 43 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 100 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 85 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 100 196 4 21 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 100 196 (accept_3_3 83 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 100 196 2 41 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 100 196 (Polychromatic418967fa.accept_15_6_10_1_1_3675 81 100 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 100 196 4 20 25 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 100 196
  (Polychromatic418967fa.accept_19_3_5_6_1_7135 79 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 100 196 2 39 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 100 196 (accept_3_3 77 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 100 196 4 19 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 100 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 100 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 100 196 2 37 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 100 196
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 73 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 100 196 4 18 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 100 196 (accept_3_3 71 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 100 196 2 35 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 100 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 100 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 100 196 4 17 25 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 100 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 100 196 2 33 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 100 196 (accept_3_3 65 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 100 196 4 16 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 100 196 (Polychromatic418967fa.accept_13_11_9_1_1_1407 63 100 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 100 196 2 31 50 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 100 196
  (Polychromatic418967fa.accept_19_4_5_6_1_11402 61 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 100 196 4 15 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 100 196 (accept_3_3 59 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 100 196 2 29 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 100 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 100 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 100 196 4 14 25 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 100 196
  (Polychromatic418967fa.accept_18_1_10_16_1_566 55 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 100 196 2 27 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 100 196 (accept_3_3 53 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 100 196 4 13 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 100 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 100 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 196 2 25 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 196 4 12 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 196 (accept_3_3 47 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 196 2 23 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 100 196 (Polychromatic418967fa.accept_13_6_9_1_1_5604 45 100 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 100 196 4 11 25 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 100 196
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 100 196 2 21 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 100 196 (accept_3_3 41 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 196 4 10 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 100 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 100 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 196 2 19 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 196
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 100 196 4 9 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 100 196 (accept_3_3 35 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  100 196 2 17 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 100 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 100 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 196 4 8 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 31
  100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 196 2 15 50 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 196 (accept_3_3 29
  100 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 196 4 7 25 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 196
  (Polychromatic418967fa.accept_21_6_16_7_1_3714 27 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 100 196 2 13 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 100 196 (Polychromatic418967fa.accept_21_4_16_7_1_11401 25 100 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 100 196 4 6 25 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 196 (accept_3_3 23 100 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 196 2 11 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 196 4 5 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 100 196 (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 100 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 196 2 9 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 196 (accept_3_3 17 100 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 196 4 4 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 100 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 100 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 100 196 2 7 50 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 100 196 4 3 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 100 196 (accept_3_3 11 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  100 196 2 5 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 100 196 (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 100 196 4 2 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 100 196 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 100 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 196 2 3 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 196 (accept_3_3 5 100 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100 196 4 1 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 100 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 100 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 196 2 1 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 196
  (Polychromatic418967fa.accept_17_1_15_9_1_1743 1 100 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 100 196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 98 99 196 (Eq.refl Bool.true) (allA_succ_of_accept 97 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 97
  99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 99 196
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 96 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 99 196 (accept_3_3 95 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  99 196 (Polychromatic418967fa.accept_21_10_15_7_1_3784 94 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 99 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 93 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 196 (accept_3_3 92 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 99 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 90 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 99 196 (accept_3_3 89 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  99 196 (Polychromatic418967fa.accept_16_8_3_4_1_3233 88 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 99 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 196 (accept_3_3 86 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 99 196
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 84 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 99 196 (accept_3_3 83 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  99 196 (Polychromatic418967fa.accept_15_7_9_1_1_473 82 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 99 196 (Polychromatic418967fa.accept_15_6_9_1_1_1823 81 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 196 (accept_3_3 80 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 99 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 78 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 99 196 (accept_3_3 77 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  99 196 (Polychromatic418967fa.accept_13_11_8_1_1_3815 76 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 99 196 (Polychromatic418967fa.accept_10_5_9_6_1_697 75 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 196 (accept_3_3 74 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 99 196
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 72 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 99 196 (accept_3_3 71 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  99 196 (Polychromatic418967fa.accept_13_5_8_1_1_2161 70 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 99 196 (Polychromatic418967fa.accept_18_15_9_16_1_6029 69 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 196 (accept_3_3 68 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 99 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 99 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 99 196 (accept_3_3 65 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  99 196 (Polychromatic418967fa.accept_13_12_8_1_1_825 64 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 99 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 196 (accept_3_3 62 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 99 196
  (Polychromatic418967fa.accept_16_12_3_4_1_4317 60 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 99 196 (accept_3_3 59 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  99 196 (Polychromatic418967fa.accept_13_6_8_1_1_2913 58 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 99 196 (Polychromatic418967fa.accept_13_5_8_1_1_2161 57 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 196 (accept_3_3 56 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 99 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 99 196 (accept_3_3 53 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  99 196 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 99 196 (Polychromatic418967fa.accept_13_12_8_1_1_825 51 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 196 (accept_3_3 50 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 196
  (Polychromatic418967fa.accept_13_9_8_1_1_824 48 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 99 196 (accept_3_3 47 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  99 196 (Polychromatic418967fa.accept_13_7_8_1_1_2145 46 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 99 196 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 196 (accept_3_3 44 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 99 196 (accept_3_3 41 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  99 196 (Polychromatic418967fa.accept_15_10_9_1_1_3688 40 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 99 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 196 (accept_3_3 38 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 196
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 99 196 (accept_3_3 35 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  99 196 (Polychromatic418967fa.accept_19_15_4_6_1_8666 34 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 99 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 196 (accept_3_3 32 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 99 196 (accept_3_3 29 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  99 196 (Polychromatic418967fa.accept_16_12_3_4_1_4317 28 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 99 196 (Polychromatic418967fa.accept_22_5_11_20_1_11400 27 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 196 (accept_3_3 26 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 99 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 196
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 99 196 (accept_3_3 23 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  99 196 (Polychromatic418967fa.accept_13_9_8_1_1_824 22 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 99 196 (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 196 (accept_3_3 20 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 99 196 (accept_3_3 17 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  99 196 (Polychromatic418967fa.accept_22_16_11_20_1_11399 16 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 99 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 196 (accept_3_3 14 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 196
  (Polychromatic418967fa.accept_13_12_8_1_1_825 12 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 99 196 (accept_3_3 11 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  99 196 (Polychromatic418967fa.accept_15_10_9_1_1_3688 10 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 99 196 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 196 (accept_3_3 8 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 196 (accept_3_3 5 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  196 (Polychromatic418967fa.accept_17_4_14_9_1_5105 4 99 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 196 (accept_3_3 2 99 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 99 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  196 (allA_of_3_1 98 98 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 196 (allA_succ_of_accept 96 97 196
  (Polychromatic418967fa.accept_13_5_6_1_1_822 96 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 196 (accept_3_3 95 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 94 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 196 (accept_3_3 92 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 196 (Polychromatic418967fa.accept_10_1_7_6_1_91 91 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 196
  (Polychromatic418967fa.accept_17_5_12_9_1_10091 90 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 196 (accept_3_3 89 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 196 (Polychromatic418967fa.accept_16_8_1_4_1_6622 88 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 196 (accept_3_3 86 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 85 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 196
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 84 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 196 (accept_3_3 83 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 196 (accept_3_3 80 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 196 (Polychromatic418967fa.accept_19_3_2_6_1_11398 79 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 196
  (Polychromatic418967fa.accept_16_14_1_4_1_5432 78 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 196 (accept_3_3 77 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 196 (Polychromatic418967fa.accept_16_12_1_4_1_5403 76 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 196 (accept_3_3 74 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 196 (Polychromatic418967fa.accept_10_3_7_6_1_659 73 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 196
  (Polychromatic418967fa.accept_13_7_6_1_1_368 72 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 196 (accept_3_3 71 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 196 (accept_3_3 68 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 196 (Polychromatic418967fa.accept_13_2_6_1_1_3807 67 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 196
  (Polychromatic418967fa.accept_15_6_7_1_1_93 66 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 196 (accept_3_3 65 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 196 (Polychromatic418967fa.accept_23_18_5_12_1_11397 64 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 196 (accept_3_3 62 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 196
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 60 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 196 (accept_3_3 59 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 196 (accept_3_3 56 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 196 (Polychromatic418967fa.accept_13_3_6_1_1_3797 55 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 196
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 196 (accept_3_3 53 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 196 (Polychromatic418967fa.accept_21_10_13_7_1_6789 52 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 196 (accept_3_3 50 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 196 (Polychromatic418967fa.accept_25_24_22_21_1_11396 49 97 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 196
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 48 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 196 (accept_3_3 47 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 196 (accept_3_3 44 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 196 (Polychromatic418967fa.accept_10_3_7_6_1_659 43 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 196
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 196 (accept_3_3 41 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 196 (Polychromatic418967fa.accept_15_10_7_1_1_3686 40 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 196 (accept_3_3 38 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 196
  (Polychromatic418967fa.accept_15_6_7_1_1_93 36 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 196 (accept_3_3 35 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 196 (accept_3_3 32 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 196 (Polychromatic418967fa.accept_10_1_7_6_1_91 31 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 196
  (Polychromatic418967fa.accept_16_14_1_4_1_5432 30 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 196 (accept_3_3 29 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 196 (Polychromatic418967fa.accept_13_2_6_1_1_3807 28 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 196 (accept_3_3 26 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 196 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 196
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 24 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 196 (accept_3_3 23 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 196 (accept_3_3 20 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 196 (Polychromatic418967fa.accept_16_3_1_4_1_5426 19 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 196
  (Polychromatic418967fa.accept_13_5_6_1_1_822 18 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 196 (accept_3_3 17 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 196 (Polychromatic418967fa.accept_13_3_6_1_1_3797 16 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 196 (accept_3_3 14 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 196
  (Polychromatic418967fa.accept_16_12_1_4_1_5403 12 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 196 (accept_3_3 11 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 196 (accept_3_3 8 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 196 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 196
  (Polychromatic418967fa.accept_15_6_7_1_1_93 6 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 196 (accept_3_3 5 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  196 (Polychromatic418967fa.accept_17_4_12_9_1_6379 4 97 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 97 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 196 (accept_3_3 2 97 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 196 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 97 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 196
  (allA_succ_of_accept 95 96 196 (accept_3_3 95 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 96
  196 2 47 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93
  96 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 96 196 4 23 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 96 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 96 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 196 2 45 48 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 196 (accept_3_3 89 96 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 196 4 22 24 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 196
  (Polychromatic418967fa.accept_11_10_8_9_1_492 87 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 196 2 43 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 85 96 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 85 96 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 196 4 21 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 196 (accept_3_3 83 96 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 196 2 41 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 196 (Polychromatic418967fa.accept_13_3_5_1_1_2144 81 96 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 196 4 20 24 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 196
  (Polychromatic418967fa.accept_19_3_1_6_1_3114 79 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 196 2 39 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 96 196 (accept_3_3 77 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 96
  196 4 19 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  96 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 96 196 2 37 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 96 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 96 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 196 4 18 24 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 196 (accept_3_3 71 96 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 196 2 35 48 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 196
  (Polychromatic418967fa.accept_13_4_5_1_1_833 69 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 196 4 17 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 96 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 196 2 33 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 196 (accept_3_3 65 96 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 196 4 16 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 96 196 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 96 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 196 2 31 48 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 196
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 61 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 196 4 15 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 196 (accept_3_3 59 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96
  196 2 29 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  96 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 96 196 4 14 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 96 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 96 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 196 2 27 48 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 196 (accept_3_3 53 96 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 196 4 13 24 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 196
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 51 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 96 196 2 25 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 96 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 96 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 196 4 12 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 196 (accept_3_3 47 96 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 196 2 23 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 196 (Polychromatic418967fa.accept_13_6_5_1_1_834 45 96 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 196 4 11 24 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 196
  (Polychromatic418967fa.accept_11_10_8_9_1_492 43 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 196 2 21 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 196 (accept_3_3 41 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96
  196 4 10 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  96 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 96 196 2 19 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 96 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 96 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 196 4 9 24 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 196 (accept_3_3 35 96 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 196 2 17 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 196 (Polychromatic418967fa.accept_15_3_6_1_1_1834
  33 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 96 196 4 8 24 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 196 2 15 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 96 196 (accept_3_3 29 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96
  196 4 7 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  96 196 (Polychromatic418967fa.accept_21_6_12_7_1_11386 27 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 96 196 2 13 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 96 196 (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 96 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 196 4 6 24 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 196 (accept_3_3 23 96 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 196 2 11 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 196 4 5 24 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 196
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 196 2 9 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 196 (accept_3_3 17 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96
  196 4 4 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  96 196 (Polychromatic418967fa.accept_18_15_6_16_1_4730 15 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 96 196 2 7 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 96 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 96 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 196 4 3 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 196 (accept_3_3 11 96 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 196 2 5 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 96 196 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 96 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 196 4 2 24 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 196
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 196 2 3 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 196 (accept_3_3 5 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 196
  4 1 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96
  196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 96 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 196 2 1 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 96 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 196
  (allA_of_3_1 95 95 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 196 (allA_succ_of_accept 93 94 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 93 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 94 196 2 46 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 91 94 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 94 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 94 196 2 45 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 94 196 (accept_3_3 89 94 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 88 94 196 2 44 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 94 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 87 94 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 94 196 2 43 47 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 94 196
  (Polychromatic418967fa.accept_10_5_4_6_1_319 85 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 94 196 2 42 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 94 196 (accept_3_3 83 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 94
  196 2 41 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81
  94 196 (Polychromatic418967fa.accept_16_1_14_4_1_3220 81 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 94 196 2 40 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 94 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 79 94 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 94 196 2 39 47 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 94 196 (accept_3_3 77 94 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 94 196 2 38 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 94 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 75 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 94 196 2 37 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 94 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 94 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 94 196 2 36 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 94 196 (accept_3_3 71 94 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 94 196 2 35 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 94 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 94 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 94 196 2 34 47 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 94 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 94 196 2 33 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 94 196 (accept_3_3 65 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 94
  196 2 32 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  94 196 (Polychromatic418967fa.accept_13_11_3_1_1_1397 63 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 94 196 2 31 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 94 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 61 94 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 94 196 2 30 47 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 94 196 (accept_3_3 59 94 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 94 196 2 29 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 94 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 94 196 2 28 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 94 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 94 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 94 196 2 27 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 94 196 (accept_3_3 53 94 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 94 196 2 26 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 94 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 94 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 196 2 25 47 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 196 2 24 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 94 196 (accept_3_3 47 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 94
  196 2 23 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  94 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 94 196 2 22 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 94 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 43 94 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 94 196 2 21 47 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 94 196 (accept_3_3 41 94 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94 196 2 20 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 94 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 94 196 2 19 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 94 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 94 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 94 196 2 18 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 94 196 (accept_3_3 35 94 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94 196 2 17 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 94 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 94 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 196 2 16 47 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 196 2 15 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 94 196 (accept_3_3 29 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94
  196 2 14 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  94 196 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 94 196 2 13 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 94 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 94 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 196 2 12 47 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 196 (accept_3_3 23 94 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 196 2 11 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 94 196 2 10 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 94 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 94 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 196 2 9 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 196 (accept_3_3 17 94 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 94 196 2 8 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 94 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 94 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 196 2 7 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 196 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 196 2 6 47 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 196 (accept_3_3 11
  94 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 196 2 5 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 196
  (Polychromatic418967fa.accept_16_9_14_4_1_3225 9 94 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 196 2 4 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 94 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 196 2 3 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 196 (accept_3_3 5 94 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 196 2 2 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 94 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 196 2 1 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 94
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 196
  (allA_succ_of_accept 92 93 196 (accept_3_3 92 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 90 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 196 (accept_3_3 89 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 88 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 87 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 196 (accept_3_3 86 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 196 (Polychromatic418967fa.accept_11_7_5_9_1_884 84 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 196 (accept_3_3 83 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 196
  (Polychromatic418967fa.accept_8_1_5_4_1_388 81 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 196 (accept_3_3 80 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 78 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 196 (accept_3_3 77 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 196
  (Polychromatic418967fa.accept_19_18_17_6_1_5775 75 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 196 (accept_3_3 74 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 196 (Polychromatic418967fa.accept_16_8_13_4_1_3258 72 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 196 (accept_3_3 71 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 196 (Polychromatic418967fa.accept_16_6_13_4_1_643 70 93 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 69 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 196 (accept_3_3 68 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 196 (accept_3_3 65 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 196
  (Polychromatic418967fa.accept_20_3_13_16_1_641 63 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 196 (accept_3_3 62 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 196 (accept_3_3 59 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 196
  (Polychromatic418967fa.accept_8_1_5_4_1_388 57 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 196 (accept_3_3 56 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 196 (accept_3_3 53 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 196 (Polychromatic418967fa.accept_17_1_8_9_1_1810 52 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 196 (accept_3_3 50 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 196 (accept_3_3 47 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 196
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 196 (accept_3_3 44 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 196 (accept_3_3 41 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 196
  (Polychromatic418967fa.accept_10_9_3_6_1_686 39 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 196 (accept_3_3 38 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 196 (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 196 (accept_3_3 35 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 196 (Polychromatic418967fa.accept_15_4_3_1_1_487 34 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 196
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 196 (accept_3_3 32 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 196 (accept_3_3 29 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 196
  (Polychromatic418967fa.accept_10_7_3_6_1_644 27 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 196 (accept_3_3 26 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 196 (accept_3_3 23 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 196
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 196 (accept_3_3 20 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 196 (accept_3_3 17 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 196 (Polychromatic418967fa.accept_13_3_2_1_1_2907 16 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 196 (accept_3_3 14 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 196 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 196 (accept_3_3 11 93 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 93 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 196
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 196 (accept_3_3 8 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 93 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 196 (accept_3_3 5 93 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 93 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 196 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3
  93 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 196 (accept_3_3 2 93 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 196
  (allA_of_3_1 92 92 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 196 (allA_succ_of_accept 90 91 196
  (Polychromatic418967fa.accept_22_2_3_20_1_4812 90 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 91 196 (accept_3_3 89 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  91 196 (Polychromatic418967fa.accept_16_8_11_4_1_3290 88 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 91 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 91 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 196 (accept_3_3 86 91 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 91 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 91 196 7 12 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 91 196 (accept_3_3 83 91 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 91 196 (Polychromatic418967fa.accept_10_2_1_6_1_634
  82 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 91 196 (accept_3_3 80 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  91 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 79 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 91 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 91 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 91 196 7 11 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 91 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 76 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 91 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 91 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 196 (accept_3_3 74 91 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 91 196 (Polychromatic418967fa.accept_16_9_11_4_1_3194 73 91 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 196
  (Polychromatic418967fa.accept_10_2_1_6_1_634 72 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 196 (accept_3_3 71 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 91
  196 7 10 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  91 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 91 196 (accept_3_3 68 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 91 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 91 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 91 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 196 (accept_3_3 65 91 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 196 (Polychromatic418967fa.accept_18_10_1_16_1_579
  64 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 91 196 7 9 13 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 91 196 (accept_3_3 62
  91 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 196
  (Polychromatic418967fa.accept_11_6_3_9_1_906 61 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 91 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 91 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 196 (accept_3_3 59 91 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 91 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 91 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57
  91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 91 196 7 8 13 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 91 196
  (Polychromatic418967fa.accept_8_7_3_4_1_404 55 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 91 196 (Polychromatic418967fa.accept_16_6_11_4_1_635 54 91 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 196 (accept_3_3 53 91 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 91 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 91 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 196 (accept_3_3 50 91
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 91 196 7 7 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 91 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 196 (accept_3_3 47 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 91 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 196 (accept_3_3 44 91 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 196 (Polychromatic418967fa.accept_18_7_1_16_1_578 43 91 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 91 196 7 6 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 91 196 (accept_3_3 41 91 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 91 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 196 (accept_3_3 38 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 196 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 196 (Polychromatic418967fa.accept_23_13_22_12_1_11395 36 91 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 91 196 7 5 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 91 196
  (Polychromatic418967fa.accept_12_10_7_4_1_820 34 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 91 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 91 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 196 (accept_3_3 32 91 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 91 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 91 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 30
  91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 196 (accept_3_3 29 91
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 91 196 7 4 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 91 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 196 (accept_3_3 26 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 196 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 196 (accept_3_3 23 91 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 91 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 91 196 7 3 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 91 196 (accept_3_3 20 91 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 196 (Polychromatic418967fa.accept_22_19_3_20_1_11394 19 91
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 196
  (Polychromatic418967fa.accept_20_18_11_16_1_6973 18 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 91 196 (accept_3_3 17 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 91 196 (Polychromatic418967fa.accept_17_16_6_9_1_7769 16 91 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 91 196 7 2 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 91 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 91 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 196 (accept_3_3 11 91 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 91 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 91 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 91
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 196 (accept_3_3 8 91 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 91 196 7 1 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 91 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 91
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 196 (accept_3_3 5 91 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 4
  91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 196 (accept_3_3 2 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  196 (Polychromatic418967fa.accept_20_1_11_16_1_699 1 91 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 196
  (allA_succ_of_accept 89 90 196 (accept_3_3 89 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 90
  196 2 44 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87
  90 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 87 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 90 196 2 43 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 90 196 (Polychromatic418967fa.accept_19_9_14_6_1_2014 85 90 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 196 2 42 45 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 196 (accept_3_3 83 90 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 196 2 41 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 196
  (Polychromatic418967fa.accept_11_4_2_9_1_496 81 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 196 2 40 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 90 196 (Polychromatic418967fa.accept_20_19_10_16_1_7001 79 90 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 196 2 39 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 196 (accept_3_3 77 90 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 196 2 38 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 75 90 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 90 196 2 37 45 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 196
  (Polychromatic418967fa.accept_11_7_2_9_1_480 73 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 196 2 36 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 196 (accept_3_3 71 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90
  196 2 35 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  90 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 90 196 2 34 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 90 196 (Polychromatic418967fa.accept_13_2_12_1_1_343 67 90 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 196 2 33 45 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 196 (accept_3_3 65 90 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 196 2 32 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 196
  (Polychromatic418967fa.accept_12_3_6_4_1_400 63 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 196 2 31 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 90 196 (Polychromatic418967fa.accept_25_11_15_21_1_11393 61 90 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 196 2 30 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 196 (accept_3_3 59 90 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 196 2 29 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 57
  90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 196 2 28 45 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 196
  (Polychromatic418967fa.accept_20_15_10_16_1_8506 55 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 90 196 2 27 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 90 196 (accept_3_3 53 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 90 196 2 26 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 90 196 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 90 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 196 2 25 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 196 (Polychromatic418967fa.accept_19_11_14_6_1_4378
  49 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 196 2 24 45 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 196 (accept_3_3 47
  90 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 196 2 23 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 196 2 22 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 90 196 (Polychromatic418967fa.accept_19_5_14_6_1_4413 43 90 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 196 2 21 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 196 (accept_3_3 41 90 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 196 2 20 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 90 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 196 2 19 45 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 196
  (Polychromatic418967fa.accept_11_4_2_9_1_496 37 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 196 2 18 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 196 (accept_3_3 35 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90
  196 2 17 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  90 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 90 196 2 16 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 90 196 (Polychromatic418967fa.accept_13_5_12_1_1_2123 31 90 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 196 2 15 45 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 196 (accept_3_3 29 90 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 196 2 14 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 196
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 196 2 13 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 90 196 (Polychromatic418967fa.accept_20_5_10_16_1_9890 25 90 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 196 2 12 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 196 (accept_3_3 23 90 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 196 2 11 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 90 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 196 2 10 45 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 196
  (Polychromatic418967fa.accept_20_19_10_16_1_7001 19 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 90 196 2 9 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 90 196 (accept_3_3 17 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 90 196 2 8 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 90 196 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 90 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 196 2 7 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 196 (Polychromatic418967fa.accept_17_13_5_9_1_1762 13 90 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 196 2 6 45 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 196 (accept_3_3 11 90 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 196 2 5 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 9
  90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 196 2 4 45 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 196
  (Polychromatic418967fa.accept_11_7_2_9_1_480 7 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 196 2 3 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 90 196 (accept_3_3 5 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 196
  2 2 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90
  196 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 90 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 196 2 1 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 196 (Polychromatic418967fa.accept_19_1_14_6_1_1983 1 90 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 196
  (allA_of_3_1 89 89 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 196 (allA_succ_of_accept 87 88 196
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 87 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 88 196 2 43 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 85 88 196 (Polychromatic418967fa.accept_15_10_13_1_1_3698 85 88 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 88 196 4 21 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 88 196 (accept_3_3 83 88 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 82 88 196 2 41 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 88 196 (Polychromatic418967fa.accept_16_1_8_4_1_4334 81 88 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 88 196 4 20 22 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 88 196
  (Polychromatic418967fa.accept_16_15_8_4_1_1355 79 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 88 196 2 39 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 88 196 (accept_3_3 77 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 88
  196 4 19 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  88 196 (Polychromatic418967fa.accept_16_11_8_4_1_2234 75 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 88 196 2 37 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 88 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 73 88 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 88 196 4 18 22 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 88 196 (accept_3_3 71 88 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 88 196 2 35 44 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 88 196
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 69 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 88 196 4 17 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 88 196 (Polychromatic418967fa.accept_16_3_8_4_1_3279 67 88 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 88 196 2 33 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 88 196 (accept_3_3 65 88 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88 196 4 16 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 88 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 88 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 88 196 2 31 44 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 88 196
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 61 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 88 196 4 15 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 88 196 (accept_3_3 59 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88
  196 2 29 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  88 196 (Polychromatic418967fa.accept_15_12_13_1_1_3695 57 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 88 196 4 14 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 88 196 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 88 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 88 196 2 27 44 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 88 196 (accept_3_3 53 88 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88 196 4 13 22 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 88 196
  (Polychromatic418967fa.accept_16_3_8_4_1_3279 51 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 88 196 2 25 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 88 196 (Polychromatic418967fa.accept_16_1_8_4_1_4334 49 88 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 88 196 4 12 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 88 196 (accept_3_3 47 88 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88 196 2 23 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 88 196 (Polychromatic418967fa.accept_16_13_8_4_1_3250 45 88 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 88 196 4 11 22 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 88 196
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 88 196 2 21 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 88 196 (accept_3_3 41 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88
  196 4 10 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  88 196 (Polychromatic418967fa.accept_16_7_8_4_1_689 39 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 88 196 2 19 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 88 196 (Polychromatic418967fa.accept_13_11_10_1_1_1409 37 88 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 88 196 4 9 22 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 88 196 (accept_3_3 35 88 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88 196 2 17 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 88 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 33
  88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 88 196 4 8 22 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 88 196
  (Polychromatic418967fa.accept_16_15_8_4_1_1355 31 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 88 196 2 15 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 88 196 (accept_3_3 29 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88
  196 4 7 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  88 196 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 88 196 2 13 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 88 196 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 88 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 196 4 6 22 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 196 (accept_3_3 23 88 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 196 2 11 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 196 (Polychromatic418967fa.accept_16_5_8_4_1_5418
  21 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 196 4 5 22 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 196
  (Polychromatic418967fa.accept_16_3_8_4_1_3279 19 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 196 2 9 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 196 (accept_3_3 17 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  196 4 4 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 196 (Polychromatic418967fa.accept_16_15_8_4_1_1355 15 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 196 2 7 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 88 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 88 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 196 4 3 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 196 (accept_3_3 11 88 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 196 2 5 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 88 196 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 88 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 196 4 2 22 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 196
  (Polychromatic418967fa.accept_16_7_8_4_1_689 7 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 196 2 3 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 196 (accept_3_3 5 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 196
  4 1 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  196 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 88 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 88 196 2 1 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 88 196 (Polychromatic418967fa.accept_16_1_8_4_1_4334 1 88 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 88
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 196
  (allA_succ_of_accept 86 87 196 (accept_3_3 86 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 84 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 196 (accept_3_3 83 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 196
  (Polychromatic418967fa.accept_10_1_7_6_1_91 81 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 196 (accept_3_3 80 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 196 (Polychromatic418967fa.accept_11_1_10_9_1_871 78 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 196 (accept_3_3 77 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 196
  (Polychromatic418967fa.accept_8_3_7_4_1_42 75 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 196 (accept_3_3 74 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 196 (Polychromatic418967fa.accept_16_8_7_4_1_2217 72 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 196 (accept_3_3 71 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 196 (Polychromatic418967fa.accept_13_5_9_1_1_1405 70 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 196
  (Polychromatic418967fa.accept_20_9_7_16_1_4030 69 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 196 (accept_3_3 68 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 196 (accept_3_3 65 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 196
  (Polychromatic418967fa.accept_10_3_7_6_1_659 63 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 196 (accept_3_3 62 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 196 (Polychromatic418967fa.accept_13_8_9_1_1_2147 60 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 196 (accept_3_3 59 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 196 (accept_3_3 56 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 196 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 196 (accept_3_3 53 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 196 (Polychromatic418967fa.accept_11_8_10_9_1_1401 52 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 196
  (Polychromatic418967fa.accept_8_3_7_4_1_42 51 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 196 (accept_3_3 50 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 196 (accept_3_3 47 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 196
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 196 (accept_3_3 44 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 196 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 196 (accept_3_3 41 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 196 (accept_3_3 38 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 196 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 196 (accept_3_3 35 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 196 (Polychromatic418967fa.accept_11_1_10_9_1_871 34 87 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 196
  (Polychromatic418967fa.accept_10_3_7_6_1_659 33 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 196 (accept_3_3 32 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 196 (accept_3_3 29 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 196
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 196 (accept_3_3 26 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 196 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 196 (accept_3_3 23 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 87 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 196 (accept_3_3 20 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 196 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 196 (accept_3_3 17 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 196 (Polychromatic418967fa.accept_19_16_11_6_1_7149 16 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 196
  (Polychromatic418967fa.accept_13_2_9_1_1_67 15 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 196 (accept_3_3 14 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 196 (accept_3_3 11 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 87 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 196
  (Polychromatic418967fa.accept_18_9_15_16_1_8759 9 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 196 (accept_3_3 8 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 196 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 87 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 196 (accept_3_3 5 87 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 87 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 196 (accept_3_3 2 87 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 87
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 196
  (allA_of_3_1 86 86 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 196 (allA_succ_of_accept 84 85 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 196 (accept_3_3 83 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 196 (accept_3_3 80 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 196 (Polychromatic418967fa.accept_10_9_5_6_1_691 79 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 196 (accept_3_3 77 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 196 (Polychromatic418967fa.accept_11_10_8_9_1_492 76 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 196 (accept_3_3 74 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 73 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 196
  (Polychromatic418967fa.accept_16_8_5_4_1_674 72 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 196 (accept_3_3 71 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 196 (accept_3_3 68 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 196 (Polychromatic418967fa.accept_15_7_10_1_1_1836 67 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 196 (accept_3_3 65 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 196 (accept_3_3 62 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 196 (Polychromatic418967fa.accept_10_1_5_6_1_649 61 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 196 (accept_3_3 59 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 196 (accept_3_3 56 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 196
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 196 (accept_3_3 53 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 196 (Polychromatic418967fa.accept_15_7_10_1_1_1836 52 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 196 (accept_3_3 50 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 196 (accept_3_3 47 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 196 (accept_3_3 44 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 196 (Polychromatic418967fa.accept_11_10_8_9_1_492 43 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 196 (accept_3_3 41 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 196 (Polychromatic418967fa.accept_16_8_5_4_1_674 40 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 196 (accept_3_3 38 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 196
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 196 (accept_3_3 35 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 196 (accept_3_3 32 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 196 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 196 (accept_3_3 29 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 196 (accept_3_3 26 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 196 (accept_3_3 23 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 196 (accept_3_3 20 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 196
  (Polychromatic418967fa.accept_19_18_9_6_1_5815 18 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 196 (accept_3_3 17 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 196 (Polychromatic418967fa.accept_13_3_7_1_1_334 16 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 196 (accept_3_3 14 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 196 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 196 (accept_3_3 11 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 196 (accept_3_3 8 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 196 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 85 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 196 (accept_3_3 5 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  196 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 85 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 85 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 196 (accept_3_3 2 85 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 85 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 196
  (allA_succ_of_accept 83 84 196 (accept_3_3 83 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84
  196 2 41 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81
  84 196 (Polychromatic418967fa.accept_13_3_6_1_1_3797 81 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 84 196 4 20 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 84 196 (Polychromatic418967fa.accept_11_2_7_9_1_890 79 84 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 196 2 39 42 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 84 196 7 11 12 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 84 196 4 19 21 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 196
  (Polychromatic418967fa.accept_10_5_4_6_1_319 75 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 196 2 37 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 84 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 84 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 196 4 18 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 196 (accept_3_3 71 84 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 196 14 5 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 84 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 84 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 196 4 17 21 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 196 2 33 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 196 (accept_3_3 65 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84
  196 4 16 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 84
  196 7 9 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 84
  196 2 31 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61
  84 196 (Polychromatic418967fa.accept_13_9_6_1_1_2902 61 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 84 196 4 15 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 84 196 (accept_3_3 59 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 84 196 2 29 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 84 196 (Polychromatic418967fa.accept_11_2_7_9_1_890 57 84 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 196 28 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 84 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 196 2 27 42 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 196 (accept_3_3 53
  84 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 196 4 13 21 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 196 2 25 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 49 84 196 7 7 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 48 84 196 4 12 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 196 (accept_3_3 47 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84
  196 2 23 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  84 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 84 196 4 11 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 84 196 (Polychromatic418967fa.accept_23_20_15_12_1_6321 43 84 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 196 14 3 6 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 196 (accept_3_3 41 84 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 196 4 10 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 196
  (Polychromatic418967fa.accept_22_17_18_20_1_11392 39 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 84 196 2 19 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 84 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 84 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 196 4 9 21 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 84 196 7 5 12 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 84 196 2 17 42 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 196 4 8 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 84 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 196 2 15 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 196 (accept_3_3 29 84 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 196 28 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 84 196 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 84 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 196 2 13 42 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 196
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 196 4 6 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 196 (accept_3_3 23 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84
  196 2 11 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84
  196 7 3 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84
  196 4 5 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  84 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 84 196 2 9 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 84 196 (accept_3_3 17 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 84 196 4 4 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 84 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 196 14 1 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 84 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 196 4 3 21 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 196 (accept_3_3 11 84 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 196 2 5 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 196 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9
  84 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 196 4 2 21 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 84 196 7 1 12 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 84 196 2 3 42 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 196 (accept_3_3 5 84
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 196 4 1 21 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 196
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 3 84 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 84 196 2 1 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 196 (allA_of_3_1
  83 83 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 196 (allA_succ_of_accept 81 82 196
  (Polychromatic418967fa.accept_10_1_2_6_1_638 81 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 82 196 2 40 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 82 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 79 82 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 196 2 39 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 196 (accept_3_3 77 82 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 196 2 38 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 82 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 196 2 37 41 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 196
  (Polychromatic418967fa.accept_11_7_5_9_1_884 73 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 82 196 2 36 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 82 196 (accept_3_3 71 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 82
  196 2 35 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  82 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 82 196 2 34 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 82 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 82 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 82 196 2 33 41 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 82 196 (accept_3_3 65 82 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 82 196 2 32 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 82 196
  (Polychromatic418967fa.accept_17_12_14_9_1_5079 63 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 82 196 2 31 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 82 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 61 82 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 82 196 2 30 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 82 196 (accept_3_3 59 82 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 82 196 2 29 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 82 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 82 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 196 2 28 41 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 196 2 27 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 82 196 (accept_3_3 53 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82
  196 2 26 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  82 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 82 196 2 25 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 82 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 82 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 82 196 2 24 41 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 82 196 (accept_3_3 47 82 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82 196 2 23 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 82 196
  (Polychromatic418967fa.accept_23_22_13_12_1_6297 45 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 82 196 2 22 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 82 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 43 82 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 82 196 2 21 41 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82 196 (accept_3_3 41 82 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 196 2 20 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 82 196 2 19 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 82 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 82 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 82 196 2 18 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 82 196 (accept_3_3 35 82 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82 196 2 17 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 82 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 82 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 196 2 16 41 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 196 2 15 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 82 196 (accept_3_3 29 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82
  196 2 14 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  82 196 (Polychromatic418967fa.accept_22_5_16_20_1_8167 27 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 82 196 2 13 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 82 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 82 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 196 2 12 41 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 196 (accept_3_3 23 82 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 196 2 11 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 82 196 2 10 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 82 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 82 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 196 2 9 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 196 (accept_3_3 17 82 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 82 196 2 8 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 82 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 82 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 196 2 7 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 196 2 6 41 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 196 (accept_3_3 11
  82 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 196 2 5 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 196
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 196 2 4 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 196 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 82 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 196 2 3 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 196 (accept_3_3 5 82 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 196 2 2 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 82 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 196 2 1 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 1
  82 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 196
  (allA_succ_of_accept 80 81 196 (accept_3_3 80 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 78 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 196 (accept_3_3 77 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 196 (Polychromatic418967fa.accept_13_11_3_1_1_1397 76 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 196
  (Polychromatic418967fa.accept_10_5_1_6_1_672 75 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 196 (accept_3_3 74 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 196 (accept_3_3 71 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 196 (Polychromatic418967fa.accept_13_5_3_1_1_1398 70 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 196
  (Polychromatic418967fa.accept_8_5_1_4_1_628 69 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 196 (accept_3_3 68 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 196 (accept_3_3 65 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 196 (Polychromatic418967fa.accept_19_7_5_6_1_9961 64 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 196
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 63 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 196 (accept_3_3 62 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 196 (Polychromatic418967fa.accept_16_12_1_4_1_5403 60 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 196 (accept_3_3 59 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 196 (Polychromatic418967fa.accept_13_6_3_1_1_1413 58 81 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 196
  (Polychromatic418967fa.accept_10_7_1_6_1_673 57 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 196 (accept_3_3 56 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 196 (accept_3_3 53 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 196
  (Polychromatic418967fa.accept_16_3_1_4_1_5426 51 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 196 (accept_3_3 50 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 196 (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 196 (accept_3_3 47 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 196 (Polychromatic418967fa.accept_11_2_4_9_1_484 46 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 196
  (Polychromatic418967fa.accept_8_5_1_4_1_628 45 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 196 (accept_3_3 44 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 196 (accept_3_3 41 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 196 (Polychromatic418967fa.accept_15_10_6_1_1_3707 40 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 196
  (Polychromatic418967fa.accept_15_9_6_1_1_493 39 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 196 (accept_3_3 38 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 196 (Polychromatic418967fa.accept_21_15_18_7_1_5161 36 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 196 (accept_3_3 35 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 196 (Polychromatic418967fa.accept_19_15_5_6_1_5760 34 81
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 196
  (Polychromatic418967fa.accept_13_7_3_1_1_814 33 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 196 (accept_3_3 32 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 196 (accept_3_3 29 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 196 (Polychromatic418967fa.accept_13_2_3_1_1_3823 28 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 196
  (Polychromatic418967fa.accept_10_7_1_6_1_673 27 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 196 (accept_3_3 26 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 196 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 196 (accept_3_3 23 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 196
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 196 (accept_3_3 20 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 196 (accept_3_3 17 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 196 (Polychromatic418967fa.accept_17_16_13_9_1_11391 16 81 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 196
  (Polychromatic418967fa.accept_10_5_1_6_1_672 15 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 196 (accept_3_3 14 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 196 (accept_3_3 11 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 196 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 81 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 196
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 196 (accept_3_3 8 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 81 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 196 (accept_3_3 5 81 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 196 (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 81 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 196 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3
  81 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 196 (accept_3_3 2 81 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 196 (allA_of_3_1 80
  80 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 196 (allA_succ_of_accept 78 79 196
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 78 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 196 (accept_3_3 77 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 196 (Polychromatic418967fa.accept_16_12_15_4_1_5422 76 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 196 (accept_3_3 74 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 73 79 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 196
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 72 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 196 (accept_3_3 71 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 196 (Polychromatic418967fa.accept_11_4_2_9_1_496 70 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 196 (accept_3_3 68 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 79 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 196
  (Polychromatic418967fa.accept_19_9_3_6_1_11390 66 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 196 (accept_3_3 65 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 196 (Polychromatic418967fa.accept_19_7_3_6_1_8663 64 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 196 (accept_3_3 62 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 196 (Polychromatic418967fa.accept_19_4_3_6_1_11389 61 79 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 196
  (Polychromatic418967fa.accept_16_12_15_4_1_5422 60 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 196 (accept_3_3 59 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 196 (accept_3_3 56 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 196 (Polychromatic418967fa.accept_10_5_9_6_1_697 55 79 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 196
  (Polychromatic418967fa.accept_17_3_11_9_1_5100 54 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 196 (accept_3_3 53 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 196 (Polychromatic418967fa.accept_21_10_16_7_1_11388 52 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 196 (accept_3_3 50 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 196 (Polychromatic418967fa.accept_20_9_19_16_1_11366 49 79 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 196
  (Polychromatic418967fa.accept_11_4_2_9_1_496 48 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 196 (accept_3_3 47 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 196 (accept_3_3 44 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 79 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 196
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 42 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 196 (accept_3_3 41 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 196 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 196 (accept_3_3 38 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 196 (Polychromatic418967fa.accept_11_4_2_9_1_496 37 79 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 196
  (Polychromatic418967fa.accept_17_2_11_9_1_1739 36 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 196 (accept_3_3 35 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 196 (accept_3_3 32 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 196 (Polychromatic418967fa.accept_21_10_16_7_1_11388 31 79 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 196
  (Polychromatic418967fa.accept_16_14_15_4_1_3268 30 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 196 (accept_3_3 29 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 196 (Polychromatic418967fa.accept_16_12_15_4_1_5422 28 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 196 (accept_3_3 26 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 196 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 79 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 196
  (Polychromatic418967fa.accept_16_8_15_4_1_5402 24 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 196 (accept_3_3 23 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 196 (accept_3_3 20 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 79 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 196
  (Polychromatic418967fa.accept_11_7_2_9_1_480 18 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 196 (accept_3_3 17 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 196 (Polychromatic418967fa.accept_19_16_3_6_1_1941 16 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 196 (accept_3_3 14 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 79 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 196
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 12 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 196 (accept_3_3 11 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 196 (accept_3_3 8 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 196 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 79 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 196
  (Polychromatic418967fa.accept_21_6_16_7_1_3714 6 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 196 (accept_3_3 5 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  196 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 79 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 196 (accept_3_3 2 79 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 196 (Polychromatic418967fa.accept_18_1_7_16_1_1342 1 79 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 196
  (allA_succ_of_accept 77 78 196 (accept_3_3 77 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78
  196 2 38 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  78 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 78 196 2 37 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 78 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 78 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 196 2 36 39 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 196 (accept_3_3 71 78 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 196 2 35 39 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 69 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 196 2 34 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 78 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 78 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 196 2 33 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 196 (accept_3_3 65 78 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 196 2 32 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 78 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 196 2 31 39 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 196
  (Polychromatic418967fa.accept_19_4_2_6_1_7181 61 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 196 2 30 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 196 (accept_3_3 59 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78
  196 2 29 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  78 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 78 196 2 28 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 78 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 78 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 196 2 27 39 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 196 (accept_3_3 53 78 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 196 2 26 39 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 196
  (Polychromatic418967fa.accept_12_3_6_4_1_400 51 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 196 2 25 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 78 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 78 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 196 2 24 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 196 (accept_3_3 47 78 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 196 2 23 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 78 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 196 2 22 39 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 196
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 196 2 21 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 196 (accept_3_3 41 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78
  196 2 20 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  78 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 78 196 2 19 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 78 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 78 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 196 2 18 39 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 196 (accept_3_3 35 78 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 196 2 17 39 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 196
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 196 2 16 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 78 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 78 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 196 2 15 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 196 (accept_3_3 29 78 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 196 2 14 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 78 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 196 2 13 39 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 196
  (Polychromatic418967fa.accept_16_9_14_4_1_3225 25 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 196 2 12 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 196 (accept_3_3 23 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78
  196 2 11 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  78 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 78 196 2 10 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 78 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 78 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 196 2 9 39 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 196 (accept_3_3 17 78 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 196 2 8 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 78 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 196 2 7 39 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 196 2 6 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 196 (accept_3_3 11 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78
  196 2 5 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  78 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 78 196 2 4 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 78 196 (Polychromatic418967fa.accept_16_7_14_4_1_1362 7 78 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 196 2 3 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 196 (accept_3_3 5 78 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 196 2 2 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 78 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 78 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 196 2 1 39 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 196
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 196
  (allA_of_3_1 77 77 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 196 (allA_succ_of_accept 75 76 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 75 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 76 196 2 37 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 76 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 76 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 196 4 18 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 196 (accept_3_3 71 76 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 196 2 35 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 76 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 196 4 17 19 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 196
  (Polychromatic418967fa.accept_11_1_10_9_1_871 67 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 196 2 33 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 76 196 (accept_3_3 65 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76
  196 4 16 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  76 196 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 76 196 2 31 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 76 196 (Polychromatic418967fa.accept_13_9_11_1_1_1375 61 76 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 196 4 15 19 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 196 (accept_3_3 59 76 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 196 2 29 38 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 76 196 4 14 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 76 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 196 2 27 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 196 (accept_3_3 53 76 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 196 4 13 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 76 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 196 2 25 38 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 196
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 49 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 196 4 12 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 196 (accept_3_3 47 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  196 2 23 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  76 196 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 196 4 11 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 196 (Polychromatic418967fa.accept_16_11_12_4_1_3195 43 76 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 196 2 21 38 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 196 (accept_3_3 41 76 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 196 4 10 19 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 196 2 19 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 76 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 196 4 9 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 196 (accept_3_3 35 76 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 76 196 2 17 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 76 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 76 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 196 4 8 19 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 196
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 31 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 196 2 15 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 196 (accept_3_3 29 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  196 4 7 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 196 (Polychromatic418967fa.accept_16_11_12_4_1_3195 27 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 196 2 13 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 196 (Polychromatic418967fa.accept_13_12_11_1_1_2920 25 76 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 196 4 6 19 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 196 (accept_3_3 23 76 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 196 2 11 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 21
  76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 196 4 5 19 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 196
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 196 2 9 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 196 (accept_3_3 17 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  196 4 4 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 196 2 7 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 76 196 (Polychromatic418967fa.accept_16_13_12_4_1_4323 13 76 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 196 4 3 19 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 196 (accept_3_3 11 76 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 196 2 5 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 196 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 76 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 196 4 2 19 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 196
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 196 2 3 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 196 (accept_3_3 5 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 196
  4 1 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  196 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 76 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 196 2 1 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 196 (allA_succ_of_accept
  74 75 196 (accept_3_3 74 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 196
  (Polychromatic418967fa.accept_6_1_3_4_1_1 73 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 196 (Polychromatic418967fa.accept_16_8_11_4_1_3290 72 75 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 196 (accept_3_3 71 75 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 196 (Polychromatic418967fa.accept_16_6_11_4_1_635 70 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 69
  75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 196 (accept_3_3 68 75
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 196 (Polychromatic418967fa.accept_6_1_3_4_1_1
  67 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 75 196 (accept_3_3 65 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  75 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 75 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 196 (accept_3_3 62 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 75 196 (accept_3_3 59 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  75 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 75 196 (Polychromatic418967fa.accept_16_9_11_4_1_3194 57 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 196 (accept_3_3 56 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 75 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 196
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 196 (accept_3_3 53 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 196 (Polychromatic418967fa.accept_27_25_21_7_1_11387 52 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 196 (accept_3_3 50 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 196
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 48 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 196 (accept_3_3 47 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  75 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 196 (Polychromatic418967fa.accept_19_7_18_6_1_3095 45 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 196 (accept_3_3 44 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 196 (accept_3_3 41 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 196 (accept_3_3 38 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 196
  (Polychromatic418967fa.accept_17_2_7_9_1_2796 36 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 196 (accept_3_3 35 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 196 (accept_3_3 32 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 196 (accept_3_3 29 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 196 (Polychromatic418967fa.accept_21_6_12_7_1_11386 27 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 196 (accept_3_3 26 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 75 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 196 (accept_3_3 23 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 196 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 196 (accept_3_3 20 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 196 (accept_3_3 17 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 196 (Polychromatic418967fa.accept_21_16_12_7_1_11385 16 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 196 (accept_3_3 14 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 196
  (Polychromatic418967fa.accept_16_12_11_4_1_1359 12 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 196 (accept_3_3 11 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 196 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 196 (accept_3_3 8 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 196 (accept_3_3 5 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  196 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 75 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 196 (Polychromatic418967fa.accept_19_3_18_6_1_3112 3 75 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 196 (accept_3_3 2 75 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 75 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 196 (allA_of_3_1 74 74
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 196 (allA_succ_of_accept 72 73 196
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 72 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 196 (accept_3_3 71 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 196 (accept_3_3 68 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 73 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 196 (accept_3_3 65 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 196 (Polychromatic418967fa.accept_13_12_8_1_1_825 64 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 196 (accept_3_3 62 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 73 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 196 (accept_3_3 59 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 196 (accept_3_3 56 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 196 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 73 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 196
  (Polychromatic418967fa.accept_23_8_4_12_1_11384 54 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 196 (accept_3_3 53 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 196 (Polychromatic418967fa.accept_23_6_4_12_1_11383 52 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 196 (accept_3_3 50 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 73 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 196 (accept_3_3 47 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 196 (Polychromatic418967fa.accept_11_2_7_9_1_890 46 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 196 (accept_3_3 44 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 196 (Polychromatic418967fa.accept_16_11_9_4_1_5438 43 73 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 196 (accept_3_3 41 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 196 (accept_3_3 38 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 73 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 196
  (Polychromatic418967fa.accept_21_15_10_7_1_9837 36 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 196 (accept_3_3 35 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 196 (accept_3_3 32 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 73 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 196 (accept_3_3 29 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 196 (accept_3_3 26 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 196 (Polychromatic418967fa.accept_13_12_8_1_1_825 25 73 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 196 (accept_3_3 23 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 196 (accept_3_3 20 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 196 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 73 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 196
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 196 (accept_3_3 17 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 196 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 196 (accept_3_3 14 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 73 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 196 (accept_3_3 11 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 196 (accept_3_3 8 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 196 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 73 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 196 (accept_3_3 5 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  196 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 73 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 73 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 196 (accept_3_3 2 73 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 196 (Polychromatic418967fa.accept_21_1_10_7_1_11382 1 73 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 196 (allA_succ_of_accept 71
  72 196 (accept_3_3 71 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 196 2 35 36 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 196
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 69 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 196 4 17 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 72 196 (Polychromatic418967fa.accept_16_3_8_4_1_3279 67 72 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 196 2 33 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 196 (accept_3_3 65 72 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 196 4 16 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 196 (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 72 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 196 2 31 36 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 196
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 196 4 15 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 196 (accept_3_3 59 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72
  196 2 29 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  72 196 (Polychromatic418967fa.accept_16_9_8_4_1_1354 57 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 72 196 4 14 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 72 196 (Polychromatic418967fa.accept_13_3_7_1_1_334 55 72 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 196 2 27 36 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 196 (accept_3_3 53 72 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 196 4 13 18 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 196
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 196 2 25 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 72 196 (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 72 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 196 4 12 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 196 (accept_3_3 47 72 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 196 2 23 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 196 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 72 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 196 4 11 18 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 196
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 43 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 196 2 21 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 196 (accept_3_3 41 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72
  196 4 10 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  72 196 (Polychromatic418967fa.accept_16_7_8_4_1_689 39 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 72 196 2 19 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 72 196 (Polychromatic418967fa.accept_13_11_7_1_1_1386 37 72 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 196 4 9 18 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 196 (accept_3_3 35 72 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 196 2 17 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 196 (Polychromatic418967fa.accept_16_1_8_4_1_4334
  33 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 196 4 8 18 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 196
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 196 2 15 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 72 196 (accept_3_3 29 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72
  196 4 7 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  72 196 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 72 196 2 13 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 72 196 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 72 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 196 4 6 18 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 196 (accept_3_3 23 72 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 196 2 11 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 21
  72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 196 4 5 18 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 196
  (Polychromatic418967fa.accept_13_6_7_1_1_335 19 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 196 2 9 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 196 (accept_3_3 17 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72
  196 4 4 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  72 196 (Polychromatic418967fa.accept_16_15_8_4_1_1355 15 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 72 196 2 7 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 72 196 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 72 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 196 4 3 18 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 196 (accept_3_3 11 72 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 196 2 5 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 196 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 72 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 196 4 2 18 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 196
  (Polychromatic418967fa.accept_16_7_8_4_1_689 7 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 196 2 3 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 196 (accept_3_3 5 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 196
  4 1 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72
  196 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 72 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 72 196 2 1 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 72 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 72 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 196 (allA_of_3_1 71 71 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 196 (allA_succ_of_accept 69 70 196
  (Polychromatic418967fa.accept_13_4_5_1_1_833 69 70 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 196 2 34 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 70 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 67 70 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 196 2 33 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 196 (accept_3_3 65 70 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 196 2 32 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 70 196 7 9 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 70 196 2 31 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 61 70 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 196 2 30 35 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 196 (accept_3_3 59
  70 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70 196 2 29 35 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 70 196
  (Polychromatic418967fa.accept_11_2_4_9_1_484 57 70 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 70 196 14 4 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 70 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 55 70 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 70 196 2 27 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 196 (accept_3_3 53 70 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 196 2 26 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 196 (Polychromatic418967fa.accept_13_12_5_1_1_1383 51 70 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 196 2 25 35 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 70 196 7 7 10 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 70 196 2 24 35 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 196 (accept_3_3 47
  70 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 196 2 23 35 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 196
  (Polychromatic418967fa.accept_13_6_5_1_1_834 45 70 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 70 196 2 22 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 70 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 43 70 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 196 14 3 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 196 (accept_3_3 41 70 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 70 196 2 20 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 70 196 (Polychromatic418967fa.accept_15_9_10_1_1_1062 39 70 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 196 2 19 35 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 70 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 196 2 18 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 70 196 7 5 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 70 196 2 17 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 70 196 (Polychromatic418967fa.accept_25_8_20_21_1_11381 33 70 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 196 2 16 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 196 (Polychromatic418967fa.accept_12_7_10_4_1_382
  31 70 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 196 2 15 35 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 196 (accept_3_3 29
  70 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 196 14 2 5 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 196
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 70 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 70 196 2 13 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 70 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 70 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 196 2 12 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 196 (accept_3_3 23 70 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 196 2 11 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 70 196 7 3 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 70 196 2 10 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 70 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 196 2 9 35 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 196 (accept_3_3 17 70 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 196 2 8 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 70 196 (Polychromatic418967fa.accept_19_15_13_6_1_8636
  15 70 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 196 14 1 5 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 196
  (Polychromatic418967fa.accept_11_2_4_9_1_484 13 70 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 70 196 2 6 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 70 196 (accept_3_3 11 70 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  196 2 5 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 196 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 70 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 70 196 2 4 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 7 70 196 7 1 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 70 196 2 3 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 70 196 (accept_3_3 5 70 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 70 196 2 2 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 70 196 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 70 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 196 2 1 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 70 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 196 (allA_succ_of_accept 68 69
  196 (accept_3_3 68 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 196
  (Polychromatic418967fa.accept_6_1_3_4_1_1 67 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 69 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 196 (accept_3_3 65 69 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 63
  69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 196 (accept_3_3 62 69
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 196 (Polychromatic418967fa.accept_6_1_3_4_1_1
  61 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 69 196
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 60 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 69 196 (accept_3_3 59 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  69 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 69 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 196 (accept_3_3 56 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 69 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 69 196 (accept_3_3 53 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  69 196 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 69 196 (Polychromatic418967fa.accept_15_6_9_1_1_1823 51 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 196 (accept_3_3 50 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 69 196 (accept_3_3 47 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  69 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 69 196 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 196 (accept_3_3 44 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 69 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 196 (accept_3_3 41 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  69 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 196 (accept_3_3 38 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 196
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 196 (accept_3_3 35 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  69 196 (Polychromatic418967fa.accept_19_15_12_6_1_8634 34 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 196 (accept_3_3 32 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 69 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 69 196 (accept_3_3 29 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  69 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 69 196 (Polychromatic418967fa.accept_17_10_1_9_1_11372 27 69 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 196 (accept_3_3 26 69 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 196
  (Polychromatic418967fa.accept_16_8_5_4_1_674 24 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 69 196 (accept_3_3 23 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  69 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 69 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 196 (accept_3_3 20 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 69 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 196 (accept_3_3 17 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  69 196 (Polychromatic418967fa.accept_13_3_4_1_1_363 16 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 196 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 196 (accept_3_3 14 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 196 (accept_3_3 11 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  69 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 196 (accept_3_3 8 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 69 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 196
  (Polychromatic418967fa.accept_11_6_3_9_1_906 6 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 196 (accept_3_3 5 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  196 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 69 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 69 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 196 (accept_3_3 2 69 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 196 (allA_of_3_1 68 68 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 196 (allA_succ_of_accept 66 67 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 196 (accept_3_3 65 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 196 (accept_3_3 62 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 196 (Polychromatic418967fa.accept_10_1_7_6_1_91 61 67 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 196 (accept_3_3 59 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 196 (accept_3_3 56 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 67 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 196
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 196 (accept_3_3 53 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 196 (Polychromatic418967fa.accept_19_14_10_6_1_4372 52 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 196 (accept_3_3 50 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 196 (Polychromatic418967fa.accept_16_1_3_4_1_665 49 67 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 196 (accept_3_3 47 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 196 (accept_3_3 44 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 196 (Polychromatic418967fa.accept_10_3_7_6_1_659 43 67 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 196 (accept_3_3 41 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 196 (Polychromatic418967fa.accept_15_10_7_1_1_3686 40 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 196 (accept_3_3 38 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 67 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 196
  (Polychromatic418967fa.accept_15_6_7_1_1_93 36 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 196 (accept_3_3 35 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 196 (accept_3_3 32 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 67 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 196 (accept_3_3 29 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 196 (accept_3_3 26 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 196 (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 67 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 196 (accept_3_3 23 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 196 (accept_3_3 20 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 67 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 196
  (Polychromatic418967fa.accept_21_18_4_7_1_8346 18 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 196 (accept_3_3 17 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 196 (Polychromatic418967fa.accept_13_3_2_1_1_2907 16 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 196 (accept_3_3 14 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 196 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 67 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 196 (accept_3_3 11 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 196 (accept_3_3 8 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 67 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 196 (accept_3_3 5 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  196 (Polychromatic418967fa.accept_19_4_10_6_1_11380 4 67 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 196 (accept_3_3 2 67 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 67 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 196 (allA_succ_of_accept 65 66
  196 (accept_3_3 65 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 196 2 32 33 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 196
  (Polychromatic418967fa.accept_12_3_6_4_1_400 63 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 196 2 31 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 196 (Polychromatic418967fa.accept_20_1_6_16_1_6991 61 66 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 196 2 30 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 196 (accept_3_3 59 66 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 196 2 29 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 66 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 196 2 28 33 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 196 2 27 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 196 (accept_3_3 53 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66
  196 2 26 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  66 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 66 196 2 25 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 66 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 66 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 196 2 24 33 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 196 (accept_3_3 47 66 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 196 2 23 33 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 196 2 22 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 196 (Polychromatic418967fa.accept_21_1_3_7_1_3727 43 66 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 196 2 21 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 196 (accept_3_3 41 66 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 196 2 20 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 66 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 196 2 19 33 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 196 2 18 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 196 (accept_3_3 35 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66
  196 2 17 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  66 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 66 196 2 16 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 66 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 66 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 196 2 15 33 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 196 (accept_3_3 29 66 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 196 2 14 33 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 196
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 196 2 13 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 196 (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 66 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 196 2 12 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 196 (accept_3_3 23 66 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 196 2 11 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 66 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 196 2 10 33 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 196 2 9 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 196 (accept_3_3 17 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  196 2 8 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 196 2 7 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 66 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 66 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 196 2 6 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 196 (accept_3_3 11 66 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 196 2 5 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 66 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 66 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 196 2 4 33 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 196
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 196 2 3 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 196 (accept_3_3 5 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 196
  2 2 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66
  196 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 66 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 66 196 2 1 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 66 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 196 (allA_of_3_1 65 65 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 196
  (allA_succ_of_accept 63 64 196 (Polychromatic418967fa.accept_13_11_12_1_1_2154 63 64 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 64 196 2 31 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 64 196 (Polychromatic418967fa.accept_17_10_13_9_1_3913
  61 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 196 4 15 16 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 196 (accept_3_3 59
  64 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 196 2 29 32 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 57 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 196 4 14 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 55 64 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 196 2 27 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 196 (accept_3_3 53 64 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 196 4 13 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 64 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 196 2 25 32 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 196 4 12 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 196 (accept_3_3 47 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  196 2 23 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 196 4 11 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 196 (Polychromatic418967fa.accept_19_5_7_6_1_11379 43 64 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 196 2 21 32 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 196 (accept_3_3 41 64 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 196 4 10 16 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 64 196 2 19 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 64 196 (Polychromatic418967fa.accept_13_11_12_1_1_2154 37 64 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 196 4 9 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 196 (accept_3_3 35 64 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 64 196 2 17 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 64 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 64 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 196 4 8 16 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 196 2 15 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 196 (accept_3_3 29 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  196 4 7 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 196 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 196 2 13 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 64 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 196 4 6 16 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 196 (accept_3_3 23 64 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 196 2 11 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 21
  64 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 196 4 5 16 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 196
  (Polychromatic418967fa.accept_18_1_10_16_1_566 19 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 196 2 9 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 196 (accept_3_3 17 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  196 4 4 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 196 2 7 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 64 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 64 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 196 4 3 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 196 (accept_3_3 11 64 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 196 2 5 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 64 196 (Polychromatic418967fa.accept_23_9_18_12_1_9751 9 64 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 196 4 2 16 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 196
  (Polychromatic418967fa.accept_23_7_18_12_1_11378 7 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 64 196 2 3 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 64 196 (accept_3_3 5 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 196
  4 1 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64
  196 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 64 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 196 2 1 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 196 (Polychromatic418967fa.accept_18_1_10_16_1_566 1 64 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 63 196 (allA_succ_of_accept 62 63 196 (accept_3_3 62 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 63 196 (Polychromatic418967fa.accept_13_8_11_1_1_3789 60 63
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 196 (accept_3_3 59 63 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 196 (Polychromatic418967fa.accept_10_8_3_6_1_685
  58 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 196
  (Polychromatic418967fa.accept_10_7_3_6_1_644 57 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 63 196 7 8 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 63 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 196 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 63 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 196 (accept_3_3 53 63 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 196
  (Polychromatic418967fa.accept_22_8_19_20_1_8208 52 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 63 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 196 (accept_3_3 50 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 49 63 196 7 7 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 48 63 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 63 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 196 (accept_3_3 47 63 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 196 (Polychromatic418967fa.accept_13_7_11_1_1_2903 46 63 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 196
  (Polychromatic418967fa.accept_22_1_19_20_1_11377 45 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 63 196 (accept_3_3 44 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 196 7 6 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 196 (accept_3_3 41 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 63 196 (Polychromatic418967fa.accept_16_8_15_4_1_5402 40 63 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 196
  (Polychromatic418967fa.accept_10_9_3_6_1_686 39 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 196 (accept_3_3 38 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 196 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 63 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 63 196 7 5 9 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 63 196
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 34 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 63 196 (Polychromatic418967fa.accept_13_7_11_1_1_2903 33 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 196 (accept_3_3 32 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 63 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 196 (Polychromatic418967fa.accept_12_6_3_4_1_394
  30 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 196 (accept_3_3 29
  63 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63 196 7 4 9 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 63 196
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 196 (accept_3_3 26 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 196 (Polychromatic418967fa.accept_16_8_15_4_1_5402 24 63 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 196 (accept_3_3 23 63 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 196 (Polychromatic418967fa.accept_13_9_11_1_1_1375 22 63
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 196 7 3 9 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 196 (accept_3_3 20
  63 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 196
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 63 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 196 (accept_3_3 17 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 63 196 (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 63 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 196
  (Polychromatic418967fa.accept_18_15_9_16_1_6029 15 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 63 196 7 2 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 63 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 196 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 63
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 196 (accept_3_3 11 63 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 196 (Polychromatic418967fa.accept_11_10_8_9_1_492
  10 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 196
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 196 (accept_3_3 8 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 196
  7 1 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 63 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 196 (accept_3_3 5 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  196 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 63 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 63 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 196 (accept_3_3 2 63 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 63 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 63 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 196 (allA_of_3_1 62 62 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 196 (allA_succ_of_accept 60 61 196
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 60 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 196 (accept_3_3 59 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 196 (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 196 (accept_3_3 56 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 196 (Polychromatic418967fa.accept_10_5_1_6_1_672 55 61 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 196
  (Polychromatic418967fa.accept_13_2_9_1_1_67 54 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 196 (accept_3_3 53 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 196 (accept_3_3 50 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 61 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 196
  (Polychromatic418967fa.accept_19_10_4_6_1_11376 48 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 196 (accept_3_3 47 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 196 (accept_3_3 44 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 196 (Polychromatic418967fa.accept_19_5_4_6_1_11375 43 61 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 196
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 196 (accept_3_3 41 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 196 (Polychromatic418967fa.accept_16_8_13_4_1_3258 40 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 196 (accept_3_3 38 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 196 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 61 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 196
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 196 (accept_3_3 35 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 196 (accept_3_3 32 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 196 (Polychromatic418967fa.accept_13_5_9_1_1_1405 31 61 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 196
  (Polychromatic418967fa.accept_17_13_10_9_1_946 30 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 196 (accept_3_3 29 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 196 (Polychromatic418967fa.accept_13_2_9_1_1_67 28 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 196 (accept_3_3 26 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 61 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 196
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 196 (accept_3_3 23 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 196 (accept_3_3 20 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 196 (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 61 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 196
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 196 (accept_3_3 17 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 196 (Polychromatic418967fa.accept_17_16_10_9_1_11361 16 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 196 (accept_3_3 14 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 196 (Polychromatic418967fa.accept_17_13_10_9_1_946 13 61 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 196
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 196 (accept_3_3 11 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 196 (accept_3_3 8 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 196 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 61 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 196
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 196 (accept_3_3 5 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  196 (Polychromatic418967fa.accept_18_4_7_16_1_2307 4 61 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 196 (accept_3_3 2 61 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 61 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 196 (allA_succ_of_accept 59 60 196
  (accept_3_3 59 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 196 2 29 30 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 60 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 60 196 4 14 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 60 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 60 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 196 2 27 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 196 (accept_3_3 53 60 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 196 4 13 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 196 (Polychromatic418967fa.accept_11_7_5_9_1_884 51 60 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 196 2 25 30 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 196 4 12 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 196 (accept_3_3 47 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60
  196 2 23 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  60 196 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 60 196 4 11 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 60 196 (Polychromatic418967fa.accept_16_11_12_4_1_3195 43 60 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 196 2 21 30 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 196 (accept_3_3 41 60 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 196 4 10 15 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 60 196 2 19 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 60 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 60 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 196 4 9 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 196 (accept_3_3 35 60 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 60 196 2 17 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 60 196 (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 60 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 196 4 8 15 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 196 2 15 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 196 (accept_3_3 29 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60
  196 4 7 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  60 196 (Polychromatic418967fa.accept_16_11_12_4_1_3195 27 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 60 196 2 13 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 60 196 (Polychromatic418967fa.accept_13_12_8_1_1_825 25 60 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 196 4 6 15 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 196 (accept_3_3 23 60 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 196 2 11 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  60 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 196 4 5 15 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 196
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 196 2 9 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 196 (accept_3_3 17 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60
  196 4 4 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  60 196 (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 60 196 2 7 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 60 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 60 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 196 4 3 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 196 (accept_3_3 11 60 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 196 2 5 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 60 196 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 60 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 196 4 2 15 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 196
  (Polychromatic418967fa.accept_11_7_5_9_1_884 7 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 196 2 3 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 196 (accept_3_3 5 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 196
  4 1 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60
  196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 60 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 196 2 1 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 60 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 196 (allA_of_3_1 59 59 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 196
  (allA_succ_of_accept 57 58 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 58 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 58 196 2 28 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 58 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 58
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 196 2 27 29 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 196 (accept_3_3 53
  58 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 196 2 26 29 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 51 58 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 58 196 2 25 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 58 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 58 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 58 196 2 24 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 58 196 (accept_3_3 47 58 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 196 2 23 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 196 (Polychromatic418967fa.accept_19_7_1_6_1_11374 45 58 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 196 2 22 29 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 196
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 58 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 196 2 21 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 58 196 (accept_3_3 41 58 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58
  196 2 20 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  58 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 58 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 58 196 2 19 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 58 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 196 2 18 29 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 196 (accept_3_3 35 58 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 196 2 17 29 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 58 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 58 196 2 16 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 58 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 58 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 196 2 15 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 196 (accept_3_3 29 58 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 196 2 14 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58 196 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 58
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 196 2 13 29 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 58 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 196 2 12 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 58 196 (accept_3_3 23 58 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58
  196 2 11 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  58 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 58 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 58 196 2 10 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 58 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 58 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 196 2 9 29 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 196 (accept_3_3 17 58 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58 196 2 8 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 58 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 58 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 196 2 7 29 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 196
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 58 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 58 196 2 6 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 58 196 (accept_3_3 11 58 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58
  196 2 5 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  58 196 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 58 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 58 196 2 4 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 58 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 58 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 196 2 3 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 196 (accept_3_3 5 58 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 196 2 2 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 58 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 58 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 196 2 1 29 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 196
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 58 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 196 (allA_succ_of_accept 56
  57 196 (accept_3_3 56 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 196
  (Polychromatic418967fa.accept_6_1_3_4_1_1 55 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 57 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 196 (accept_3_3 53 57 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 196 (Polychromatic418967fa.accept_21_10_15_7_1_3784 52 57 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 57 196 (accept_3_3 50 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  57 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 57 196 (Polychromatic418967fa.accept_11_4_2_9_1_496 48 57 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 196 (accept_3_3 47 57 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 57 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 196
  (Polychromatic418967fa.accept_8_5_1_4_1_628 45 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 57 196 (accept_3_3 44 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  57 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 57 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 57 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 196 (accept_3_3 41 57 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 57 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 196
  (Polychromatic418967fa.accept_20_19_17_16_1_2732 39 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 57 196 (accept_3_3 38 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 196 (Polychromatic418967fa.accept_25_11_7_21_1_11373 36 57
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 196 (accept_3_3 35 57 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 196 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  34 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 196 (accept_3_3 32 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  57 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 57 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 196 (accept_3_3 29 57 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 57 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 196
  (Polychromatic418967fa.accept_16_11_9_4_1_5438 27 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 196 (accept_3_3 26 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  57 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 57 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 196 (accept_3_3 23 57 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 57 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 196
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 196 (accept_3_3 20 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  57 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 196 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 57 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 196 (accept_3_3 17 57 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 196 (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 57 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 196 (accept_3_3 14 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  57 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 196 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 57 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 196 (accept_3_3 11 57 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 57 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 196
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 196 (accept_3_3 8 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57
  196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 57 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 57 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 196 (accept_3_3 5 57 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 57 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 57 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 196 (Polychromatic418967fa.accept_10_3_7_6_1_659 3
  57 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 196 (accept_3_3 2 57 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 196 (allA_of_3_1 56 56 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 55 196 (allA_succ_of_accept 54 55 196
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 196 (accept_3_3 53 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 196 (Polychromatic418967fa.accept_15_7_10_1_1_1836 52 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 196 (accept_3_3 50 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 55 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 196 (accept_3_3 47 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 196 (accept_3_3 44 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 55 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 196 (accept_3_3 41 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 196 (accept_3_3 38 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 196 (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 55 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 196
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 196 (accept_3_3 35 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 196 (accept_3_3 32 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 55 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 196 (accept_3_3 29 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 196 (Polychromatic418967fa.accept_13_2_3_1_1_3823 28 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 196 (accept_3_3 26 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 196 (Polychromatic418967fa.accept_18_7_1_16_1_578 25 55 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 196 (accept_3_3 23 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 196 (accept_3_3 20 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 55 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 196
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 196 (accept_3_3 17 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 196 (Polychromatic418967fa.accept_21_16_13_7_1_8385 16 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 196 (accept_3_3 14 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 55 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 196 (accept_3_3 11 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 196 (accept_3_3 8 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 196 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 55 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 196 (accept_3_3 5 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  196 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 55 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 196 (accept_3_3 2 55 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 196 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 55 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 196)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 196 (allA_succ_of_accept 53 54 196 (accept_3_3 53 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 196 2 26 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 54 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 196 2 25 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 196 (Polychromatic418967fa.accept_19_11_16_6_1_7155
  49 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 196 2 24 27 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 196 (accept_3_3 47
  54 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 196 2 23 27 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 196
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 196 2 22 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 196 (Polychromatic418967fa.accept_16_11_6_4_1_2228 43 54 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 196 2 21 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 196 (accept_3_3 41 54 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 196 2 20 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 54 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 196 2 19 27 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 196
  (Polychromatic418967fa.accept_15_7_9_1_1_473 37 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 196 2 18 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 54 196 (accept_3_3 35 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54
  196 2 17 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  54 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 54 196 2 16 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 54 196 (Polychromatic418967fa.accept_19_12_16_6_1_7175 31 54 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 196 2 15 27 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 196 (accept_3_3 29 54 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 196 2 14 27 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 196
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 196 2 13 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 54 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 196 2 12 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 196 (accept_3_3 23 54 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 196 2 11 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 54 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 196 2 10 27 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 196
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 196 2 9 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 196 (accept_3_3 17 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54
  196 2 8 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  54 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 54 196 2 7 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 54 196 (Polychromatic418967fa.accept_16_13_6_4_1_3277 13 54 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 196 2 6 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 196 (accept_3_3 11 54 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 196 2 5 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 54 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 54 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 196 2 4 27 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 196
  (Polychromatic418967fa.accept_15_7_9_1_1_473 7 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 196 2 3 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 196 (accept_3_3 5 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 196
  2 2 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54
  196 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 54 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 196 2 1 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 196 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 54 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 196)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  196 (allA_of_3_1 53 53 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 196 (allA_succ_of_accept 51 52 196
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 196 2 25 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 196 (Polychromatic418967fa.accept_17_15_1_9_1_10058 49 52 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 196 4 12 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 196 (accept_3_3 47 52 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 196 2 23 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 196 (Polychromatic418967fa.accept_19_7_14_6_1_9987 45 52 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 196 4 11 13 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 196
  (Polychromatic418967fa.accept_11_10_8_9_1_492 43 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 196 2 21 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 196 (accept_3_3 41 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  196 4 10 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 196 (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 196 2 19 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 196 (Polychromatic418967fa.accept_17_3_1_9_1_9012 37 52 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 196 4 9 13 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 196 (accept_3_3 35 52 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 196 2 17 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 196 (Polychromatic418967fa.accept_22_11_8_20_1_8203
  33 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 196 4 8 13 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 196
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 196 2 15 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 52 196 (accept_3_3 29 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52
  196 4 7 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  52 196 (Polychromatic418967fa.accept_17_10_1_9_1_11372 27 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 52 196 2 13 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 52 196 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 52 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 196 4 6 13 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 196 (accept_3_3 23 52 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 196 2 11 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 21
  52 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 196 4 5 13 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 196
  (Polychromatic418967fa.accept_21_19_10_7_1_8384 19 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 196 2 9 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 196 (accept_3_3 17 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  196 4 4 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 196 (Polychromatic418967fa.accept_17_15_1_9_1_10058 15 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 196 2 7 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 52 196 (Polychromatic418967fa.accept_21_13_10_7_1_3701 13 52 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 196 4 3 13 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 196 (accept_3_3 11 52 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 196 2 5 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 196 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 52 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 196 4 2 13 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 196
  (Polychromatic418967fa.accept_19_7_14_6_1_9987 7 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 52 196 2 3 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 52 196 (accept_3_3 5 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 196
  4 1 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52
  196 (Polychromatic418967fa.accept_17_3_1_9_1_9012 3 52 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 52 196 2 1 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 52 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 52 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 196))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 196 (allA_succ_of_accept 50 51 196 (accept_3_3 50 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 51 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 51 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 196 (accept_3_3 47 51 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 46
  51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 196
  (Polychromatic418967fa.accept_10_5_1_6_1_672 45 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 196 (accept_3_3 44 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 51 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 196 (accept_3_3 41 51 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 51 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 196
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 196 (accept_3_3 38 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 196 (Polychromatic418967fa.accept_19_17_13_6_1_8670 36 51 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 196 (accept_3_3 35 51 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 196 (Polychromatic418967fa.accept_13_8_12_1_1_4662 34 51
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 196
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 196 (accept_3_3 32 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 51 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 196 (accept_3_3 29 51 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 51 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 196
  (Polychromatic418967fa.accept_10_7_1_6_1_673 27 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 196 (accept_3_3 26 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 196 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 51 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 196 (accept_3_3 23 51 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 51 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 196 (accept_3_3 20 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 196 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 51 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 196 (accept_3_3 17 51 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 196 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 51 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 196
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 196 (accept_3_3 14 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 51 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 196 (accept_3_3 11 51 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 51 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 196
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 196 (accept_3_3 8 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 196 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 51 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 196 (accept_3_3 5 51 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 51 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  51 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 196 (accept_3_3 2 51 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 51
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  196))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 196 (allA_of_3_1 50 50 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 196 (allA_succ_of_accept 48 49 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 196 (accept_3_3 47 49 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 46
  49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 196 (accept_3_3 44 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 43 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 49 196 7 6 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 49 196 (accept_3_3 41 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 49 196 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 49 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 49 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 196 (accept_3_3 38 49 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 37
  49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 196
  (Polychromatic418967fa.accept_19_17_11_6_1_9996 36 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 49 196 7 5 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 49 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 49 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 196 (accept_3_3 32 49 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 196
  (Polychromatic418967fa.accept_25_6_24_21_1_11371 31 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 196 (accept_3_3 29 49 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 49 196 7 4 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 49 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 49 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 196 (accept_3_3 26 49 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 196 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 49 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 196 (accept_3_3 23 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 49 196 7 3 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 49 196 (accept_3_3 20 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 49 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 49 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 196 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 49 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 196 (accept_3_3 17 49 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 196
  (Polychromatic418967fa.accept_19_16_11_6_1_7149 16 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 49 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 49 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 49 196 7 2 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 49 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 49 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 196 (accept_3_3 11 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 196 (accept_3_3 8 49 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 49 196 7 1 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 49 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 196 (accept_3_3 5 49 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 196 (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 49 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 196 (accept_3_3 2 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 196))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 196 (allA_succ_of_accept 47 48 196
  (accept_3_3 47 48 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 196 2 23 24 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 196
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 45 48 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 196 4 11 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 43 48 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 196 2 21 24 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 196 (accept_3_3 41 48 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 196 4 10 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 196 (Polychromatic418967fa.accept_17_5_14_9_1_5104 39 48 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 196 2 19 24 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 48 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 196 4 9 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 196 (accept_3_3 35 48 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48
  196 2 17 24 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  48 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 48 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 48 196 4 8 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 48 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 48 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 196 2 15 24 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 196 (accept_3_3 29 48 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 196 4 7 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 196 (Polychromatic418967fa.accept_18_9_12_16_1_7323 27 48
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 196 2 13 24 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 196
  (Polychromatic418967fa.accept_21_4_6_7_1_3693 25 48 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 196 4 6 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 196 (accept_3_3 23 48 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48
  196 2 11 24 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  48 196 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 48 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 48 196 4 5 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 48 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 196 2 9 24 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 196 (accept_3_3 17 48 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 196 4 4 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 48 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 48 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 196 2 7 24 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 196 4 3 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 196 (accept_3_3 11 48 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48
  196 2 5 24 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  48 196 (Polychromatic418967fa.accept_18_9_12_16_1_7323 9 48 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 48 196 4 2 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 48 196 (Polychromatic418967fa.accept_23_7_2_12_1_11370 7 48 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 196 2 3 24 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 196 (accept_3_3 5 48 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 196 4 1 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 48 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 48 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 196 2 1 24 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 196)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 196 (allA_of_3_1 47 47 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 46 196 (allA_succ_of_accept 45 46 196
  (Polychromatic418967fa.accept_13_6_7_1_1_335 45 46 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 196 2 22 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 43 46 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 196 2 21 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 196 (accept_3_3 41 46 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 196 2 20 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 46 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 196 2 19 23 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 196
  (Polychromatic418967fa.accept_11_4_2_9_1_496 37 46 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 196 2 18 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 196 (accept_3_3 35 46 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46
  196 2 17 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  46 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 46 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 46 196 2 16 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 46 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 46 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 196 2 15 23 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 196 (accept_3_3 29 46 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 196 2 14 23 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 196
  (Polychromatic418967fa.accept_20_7_6_16_1_11369 27 46 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 196 2 13 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 46 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 196 2 12 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 196 (accept_3_3 23 46 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 196 2 11 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 46 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 196 2 10 23 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 46 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 196 2 9 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 196 (accept_3_3 17 46 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  196 2 8 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 46 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 196 2 7 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 46 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 46 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 196 2 6 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 196 (accept_3_3 11 46 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 196 2 5 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 46 196 (Polychromatic418967fa.accept_16_9_14_4_1_3225 9 46 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 196 2 4 23 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 196
  (Polychromatic418967fa.accept_11_7_2_9_1_480 7 46 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 46 196 2 3 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 46 196 (accept_3_3 5 46 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 196
  2 2 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46
  196 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 46 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 46 196 2 1 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 46 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 46 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 46 196)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 196
  (allA_succ_of_accept 44 45 196 (accept_3_3 44 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  45 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 45 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 45 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 196 (accept_3_3 41 45 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 196 (Polychromatic418967fa.accept_16_8_13_4_1_3258 40 45 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 196
  (Polychromatic418967fa.accept_10_9_5_6_1_691 39 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 196 (accept_3_3 38 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  45 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 45 196 (Polychromatic418967fa.accept_17_2_11_9_1_1739 36 45 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 196 (accept_3_3 35 45 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 45 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 196
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 45 196 (accept_3_3 32 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  45 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 45 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 45 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 196 (accept_3_3 29 45 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 196 (Polychromatic418967fa.accept_13_2_6_1_1_3807 28 45 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 196
  (Polychromatic418967fa.accept_19_8_7_6_1_11368 27 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 196 (accept_3_3 26 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  45 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 45 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 45 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 196 (accept_3_3 23 45 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 196 (Polychromatic418967fa.accept_13_9_6_1_1_2902 22 45 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 196
  (Polychromatic418967fa.accept_10_1_5_6_1_649 21 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 196 (accept_3_3 20 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  45 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 45 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 196 (accept_3_3 17 45 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 196 (Polychromatic418967fa.accept_13_3_6_1_1_3797 16 45 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 196
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 196 (accept_3_3 14 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  45 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 196 (Polychromatic418967fa.accept_16_12_13_4_1_3198 12 45 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 196 (accept_3_3 11 45 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 196 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 45
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 196
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 196 (accept_3_3 8 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 45 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 45 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 196 (accept_3_3 5 45 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 45 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 45 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 196 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3
  45 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 196 (accept_3_3 2 45 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  196))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 196 (allA_of_3_1 44 44 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 196 (allA_succ_of_accept 42 43 196 (Polychromatic418967fa.accept_13_3_4_1_1_363 42 43 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 196 (accept_3_3 41 43 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 196
  (Polychromatic418967fa.accept_15_10_13_1_1_3698 40 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 43 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 196 (accept_3_3 38 43 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 43 196 (Polychromatic418967fa.accept_10_7_3_6_1_644 37 43 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 196 (Polychromatic418967fa.accept_13_10_4_1_1_2142
  36 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 196 (accept_3_3 35
  43 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 196
  (Polychromatic418967fa.accept_11_1_10_9_1_871 34 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 43 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 43 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 196 (accept_3_3 32 43 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 43 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 43 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 196 (Polychromatic418967fa.accept_11_8_10_9_1_1401
  30 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 196 (accept_3_3 29
  43 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 196
  (Polychromatic418967fa.accept_10_8_3_6_1_685 28 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 43 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 196 (accept_3_3 26 43 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 43 196 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 43 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 196
  (Polychromatic418967fa.accept_16_8_11_4_1_3290 24 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 196 (accept_3_3 23 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 43 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 196 (accept_3_3 20 43 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 196 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 43 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 196
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 196 (accept_3_3 17 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 196 (Polychromatic418967fa.accept_13_3_4_1_1_363 16 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 196 (accept_3_3 14 43 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 196 (Polychromatic418967fa.accept_20_13_3_16_1_4020 13 43 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 196
  (Polychromatic418967fa.accept_11_1_10_9_1_871 12 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 196 (accept_3_3 11 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 43 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 196 (accept_3_3 8 43 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 43 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 196
  (Polychromatic418967fa.accept_16_6_11_4_1_635 6 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 196 (accept_3_3 5 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  196 (Polychromatic418967fa.accept_18_4_7_16_1_2307 4 43 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 196 (accept_3_3 2 43 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 196 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 43 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 196)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 196 (allA_succ_of_accept 41 42 196 (accept_3_3 41 42 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 196 2 20 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 42 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 42 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 196 2 19 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 37
  42 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 196 2 18 21 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 42 196 7 5 6 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 42 196 2 17 21 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 42 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 196 2 16 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 42 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 196 2 15 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 196 (accept_3_3 29 42 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 196 14 2 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 42 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 42 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 196 2 13 21 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 196
  (Polychromatic418967fa.accept_27_25_15_7_1_11367 25 42 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 42 196 2 12 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 42 196 (accept_3_3 23 42 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 196 2 11 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 42 196 7 3 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 42 196 2 10 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 196 2 9 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 196 (accept_3_3 17 42 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 196 2 8 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 42 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 196 14 1 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 13
  42 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 196 2 6 21 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 196 (accept_3_3 11
  42 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 196 2 5 21 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 42 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 196 2 4 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 42 196 7 1 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 42 196 2 3 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 196 (accept_3_3 5 42 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 196
  2 2 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42
  196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 42 196 2 1 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 196)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 196
  (allA_of_3_1 41 41 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 196 (allA_succ_of_accept 39 40 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 40 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 196 2 19 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 40 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 196 4 9 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 196 (accept_3_3 35 40 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 40 196 2 17 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 40 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 40 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 196 4 8 10 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 196
  (Polychromatic418967fa.accept_16_15_8_4_1_1355 31 40 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 196 2 15 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 196 (accept_3_3 29 40 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  196 4 7 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 196 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 40 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 196 2 13 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 196 (Polychromatic418967fa.accept_16_9_8_4_1_1354 25 40 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 196 4 6 10 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 196 (accept_3_3 23 40 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 196 2 11 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 21
  40 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 196 4 5 10 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 196
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 40 196 2 9 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 40 196 (accept_3_3 17 40 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40
  196 4 4 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  40 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 40 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 40 196 2 7 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 40 196 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 40 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 196 4 3 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 196 (accept_3_3 11 40 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 196 2 5 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 40 196 (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 40 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 196 4 2 10 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 196
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 40 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 40 196 2 3 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 40 196 (accept_3_3 5 40 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 196
  4 1 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40
  196 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 40 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 40 196 2 1 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 40 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 40 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 40 196)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 196
  (allA_succ_of_accept 38 39 196 (accept_3_3 38 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  39 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 39 196 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 39 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 196 (accept_3_3 35 39 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 196 (Polychromatic418967fa.accept_21_13_18_7_1_1216 34 39 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 196 (accept_3_3 32 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 196 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 39 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 196 (accept_3_3 29 39 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 39 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 196
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 196 (accept_3_3 26 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 39 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 196 (accept_3_3 23 39 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 39 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 196
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 196 (accept_3_3 20 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 196 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 39 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 196 (accept_3_3 17 39 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 196 (Polychromatic418967fa.accept_24_16_15_4_1_9722 16 39 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 196 (accept_3_3 14 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 196 (Polychromatic418967fa.accept_16_12_7_4_1_687 12 39 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 196 (accept_3_3 11 39 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 39 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 196
  (Polychromatic418967fa.accept_20_9_19_16_1_11366 9 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 196 (accept_3_3 8 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 39 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 196 (accept_3_3 5 39 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 39 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 39
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 196 (accept_3_3 2 39 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 39
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  196))))))))))))))))))))))))))))))))))))))) (allB_succ 38 196 (allA_of_3_1 38 38 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 196 (allA_succ_of_accept 36 37 196 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 37 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 196 (accept_3_3 35 37 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 196 (Polychromatic418967fa.accept_12_10_1_4_1_392
  34 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 196 (accept_3_3 32 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 196 (accept_3_3 29 37 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 196 (Polychromatic418967fa.accept_16_12_5_4_1_3275 28 37 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 196 (accept_3_3 26 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 37 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 196 (accept_3_3 23 37 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 37 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 196 (accept_3_3 20 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 196 (Polychromatic418967fa.accept_20_19_17_16_1_2732 19 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 196 (Polychromatic418967fa.accept_17_1_3_9_1_958 18 37 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 196 (accept_3_3 17 37 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 196 (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 37 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 196 (accept_3_3 14 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 37 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 196 (accept_3_3 11 37 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 37 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 196 (accept_3_3 8 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  196 (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 37 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 37 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 196 (accept_3_3 5 37 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 37 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 196 (accept_3_3 2 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  196 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 37 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 196))))))))))))))))))))))))))))))))))))) (allB_succ 36 196 (allA_succ_of_accept 35 36 196 (accept_3_3 35
  36 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 196 2 17 18 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 196
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 36 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 196 4 8 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 196 (Polychromatic418967fa.accept_19_12_17_6_1_11365 31 36 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 196 2 15 18 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 196 (accept_3_3 29 36 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 196 4 7 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 36 196 (Polychromatic418967fa.accept_19_8_17_6_1_5728 27 36 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 196 2 13 18 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 196
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 36 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 196 4 6 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 196 (accept_3_3 23 36 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36
  196 2 11 18 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  36 196 (Polychromatic418967fa.accept_17_4_2_9_1_3896 21 36 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 36 196 4 5 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 196 (Polychromatic418967fa.accept_21_19_15_7_1_3709 19 36 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 196 2 9 18 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 196 (accept_3_3 17 36 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 196 4 4 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 196 (Polychromatic418967fa.accept_25_15_11_21_1_11364 15 36
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 196 2 7 18 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 196
  (Polychromatic418967fa.accept_19_13_17_6_1_11363 13 36 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 36 196 4 3 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 36 196 (accept_3_3 11 36 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 196 2 5 18 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 36 196 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 36 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 196 4 2 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 196 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 36 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 196 2 3 18 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 196 (accept_3_3 5 36 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 196 4 1 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 196 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3
  36 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 196 2 1 18 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 196
  (Polychromatic418967fa.accept_21_1_15_7_1_6775 1 36 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 196)))))))))))))))))))))))))))))))))))) (allB_succ 35 196 (allA_of_3_1 35 35 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 196 (allA_succ_of_accept 33 34 196 (Polychromatic418967fa.accept_13_7_8_1_1_2145 33
  34 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 196 2 16 17 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 34 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 34 196 2 15 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 34 196 (accept_3_3 29 34 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34
  196 2 14 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  34 196 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 34 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 34 196 2 13 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 34 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 34 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 196 2 12 17 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 196 (accept_3_3 23 34 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 196 2 11 17 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 196
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 34 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 196 2 10 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 34 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 196 2 9 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 196 (accept_3_3 17 34 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 196 2 8 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 34 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 196 2 7 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 196 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 34 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 196 2 6 17 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 196 (accept_3_3 11
  34 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 196 2 5 17 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 196
  (Polychromatic418967fa.accept_13_9_8_1_1_824 9 34 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 196 2 4 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 34 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 196 2 3 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 196 (accept_3_3 5 34 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 196 2 2 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 196 (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 34 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 196 2 1 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  34 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 196))))))))))))))))))))))))))))))))))
  (allB_succ 33 196 (allA_succ_of_accept 32 33 196 (accept_3_3 32 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 33 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 33 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 196 (accept_3_3 29 33 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 28
  33 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 196
  (Polychromatic418967fa.accept_10_7_3_6_1_644 27 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 196 (accept_3_3 26 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 196 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 33 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 196 (accept_3_3 23 33 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 33 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 196
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 196 (accept_3_3 20 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 33 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 196 (accept_3_3 17 33 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 196 (Polychromatic418967fa.accept_13_3_7_1_1_334 16 33 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 196
  (Polychromatic418967fa.accept_21_15_12_7_1_5204 15 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 196 (accept_3_3 14 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 196 (accept_3_3 11 33 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 33 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 196
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 196 (accept_3_3 8 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 33 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 33 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 196 (accept_3_3 5 33 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 33 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  33 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 196 (accept_3_3 2 33 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 196)))))))))))))))))))))))))))))))))
  (allB_succ 32 196 (allA_of_3_1 32 32 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 196
  (allA_succ_of_accept 30 31 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 31 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 196 (accept_3_3 29 31 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  31 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 196 (accept_3_3 26 31
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 196
  (Polychromatic418967fa.accept_10_5_1_6_1_672 25 31 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 196 (accept_3_3 23 31 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 31 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  31 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 196 (accept_3_3 20 31
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 196 (Polychromatic418967fa.accept_8_3_7_4_1_42
  19 31 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 196
  (Polychromatic418967fa.accept_19_18_12_6_1_7187 18 31 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 196 (accept_3_3 17 31 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 196 (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 31 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 196 (accept_3_3 14 31 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 196 (Polychromatic418967fa.accept_19_13_12_6_1_11362 13 31 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 31 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 196 (accept_3_3 11 31 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 31 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 196 (accept_3_3 8 31 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 196 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 31 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 31 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 196 (accept_3_3 5 31 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  196 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 31 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 196 (accept_3_3 2 31 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 31 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 196))))))))))))))))))))))))))))))) (allB_succ 30 196
  (allA_succ_of_accept 29 30 196 (accept_3_3 29 30 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  196 2 14 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 30 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 196 2 13 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 196 (Polychromatic418967fa.accept_16_9_14_4_1_3225 25 30 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 196 2 12 15 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 196 (accept_3_3 23 30 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 196 2 11 15 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 196
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 30 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 196 2 10 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 30 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 196 2 9 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 196 (accept_3_3 17 30 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 196 2 8 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 30 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 196 2 7 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 13
  30 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 196 2 6 15 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 196 (accept_3_3 11
  30 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 196 2 5 15 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 30 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 196 2 4 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 196 (Polychromatic418967fa.accept_16_7_14_4_1_1362 7 30 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 196 2 3 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 196 (accept_3_3 5 30 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 196 2 2 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 30 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 196 2 1 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 30
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 196))))))))))))))))))))))))))))))
  (allB_succ 29 196 (allA_of_3_1 29 29 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 196
  (allA_succ_of_accept 27 28 196 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 28 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 196 2 13 14 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 196 (Polychromatic418967fa.accept_11_3_6_9_1_1378
  25 28 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 196 4 6 7 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 196 (accept_3_3 23
  28 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 196 2 11 14 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 28 196 7 3 4 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 28 196 4 5 7 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 196
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 19 28 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 196 2 9 14 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 196 (accept_3_3 17 28 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  196 4 4 7 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 28 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 196 14 1 2 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 28 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 28 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 196 4 3 7 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 196 (accept_3_3 11 28 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 196 2 5 14 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 28 196 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 28 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 196 4 2 7 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 28 196 7 1 4 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 28 196 2 3 14 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 196 (accept_3_3 5 28 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 196 4 1 7 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 28 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 196 2 1 14 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 196
  (Polychromatic418967fa.accept_16_1_12_4_1_695 1 28 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 196)))))))))))))))))))))))))))) (allB_succ 27 196 (allA_succ_of_accept 26 27 196 (accept_3_3 26 27 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25
  27 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 196
  (Polychromatic418967fa.accept_16_8_11_4_1_3290 24 27 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 196 (accept_3_3 23 27 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  27 196 (Polychromatic418967fa.accept_16_6_11_4_1_635 22 27 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 196 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 27 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 196 (accept_3_3 20 27 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 196
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 27 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 196 (accept_3_3 17 27 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  27 196 (Polychromatic418967fa.accept_17_16_10_9_1_11361 16 27 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 27 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 196 (accept_3_3 14 27 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 27 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 196
  (Polychromatic418967fa.accept_16_12_11_4_1_1359 12 27 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 196 (accept_3_3 11 27 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 196 (Polychromatic418967fa.accept_26_10_1_14_1_11360 10 27 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 196 (Polychromatic418967fa.accept_16_9_11_4_1_3194 9 27 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 196 (accept_3_3 8 27 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 27 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 196 (accept_3_3 5 27 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  196 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 27 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 196 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 27 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 196 (accept_3_3 2 27 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 27 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 196))))))))))))))))))))))))))) (allB_succ 26 196
  (allA_of_3_1 26 26 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 196 (allA_succ_of_accept 24 25 196
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 25 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 196 (accept_3_3 23 25 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 25 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 196 (accept_3_3 20 25 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 196 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 25 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 196
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 25 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 196 (accept_3_3 17 25 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 196 (Polychromatic418967fa.accept_17_16_8_9_1_1772 16 25 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 25 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 196 (accept_3_3 14 25 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 25 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 196
  (Polychromatic418967fa.accept_16_12_9_4_1_4345 12 25 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 196 (accept_3_3 11 25 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 25 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 196 (accept_3_3 8 25 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 196 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 25 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 196
  (Polychromatic418967fa.accept_11_6_3_9_1_906 6 25 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 196 (accept_3_3 5 25 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  196 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 25 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 25 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 196 (accept_3_3 2 25 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 196 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 25 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 196))))))))))))))))))))))))) (allB_succ 24 196
  (allA_succ_of_accept 23 24 196 (accept_3_3 23 24 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24
  196 2 11 12 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  24 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 24 196 4 5 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 24 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 196 2 9 12 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 196 (accept_3_3 17 24 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 196 4 4 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 24 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 24 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 196 2 7 12 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 196 4 3 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 196 (accept_3_3 11 24 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  196 2 5 12 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 196 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 24 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 24 196 4 2 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 24 196 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 24 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 196 2 3 12 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 196 (accept_3_3 5 24 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 196 4 1 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 24 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 196 2 1 12 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 196
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 24 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 196)))))))))))))))))))))))) (allB_succ 23 196 (allA_of_3_1 23 23 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 196 (allA_succ_of_accept 21 22 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 22 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 196 2 10 11 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 196
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 22 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 22 196 2 9 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 22 196 (accept_3_3 17 22 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22
  196 2 8 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  22 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 22 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 22 196 2 7 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 22 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 22 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 196 2 6 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 196 (accept_3_3 11 22 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 196 2 5 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 22 196 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 22 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 196 2 4 11 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 22 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 22 196 2 3 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 22 196 (accept_3_3 5 22 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 196
  2 2 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22
  196 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 22 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 22 196 2 1 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 22 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 22 196)))))))))))))))))))))) (allB_succ 21 196 (allA_succ_of_accept 20 21
  196 (accept_3_3 20 21 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 196
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 21 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 21 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 196 (accept_3_3 17 21 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 196 (Polychromatic418967fa.accept_22_16_21_20_1_11359 16 21 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 21 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 21 196 7 2 3 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 21 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 21 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 196 (accept_3_3 11 21 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 10
  21 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 196
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 196 (accept_3_3 8 21 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 196
  7 1 3 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 21 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 196 (accept_3_3 5 21 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  196 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 21 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 196 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 21 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 196 (accept_3_3 2 21 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 196))))))))))))))))))))) (allB_succ 20 196 (allA_of_3_1 20 20
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 196 (allA_succ_of_accept 18 19 196
  (Polychromatic418967fa.accept_13_5_6_1_1_822 18 19 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 196 (accept_3_3 17 19 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 196 (Polychromatic418967fa.accept_13_3_6_1_1_3797 16 19 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 196 (accept_3_3 14 19 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 19 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 196 (accept_3_3 11 19 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 196 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 19 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 19 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 196 (accept_3_3 8 19 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 19 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 19 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 196 (accept_3_3 5 19 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  196 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 19 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 196 (accept_3_3 2 19 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 196 (Polychromatic418967fa.accept_16_1_3_4_1_665 1 19 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 196))))))))))))))))))) (allB_succ 18 196 (allA_succ_of_accept 17
  18 196 (accept_3_3 17 18 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 196 2 8 9 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 196
  (Polychromatic418967fa.accept_12_3_6_4_1_400 15 18 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 196 2 7 9 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 18 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 196 2 6 9 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 196 (accept_3_3 11 18 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 196 2 5 9 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 18 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 196 2 4 9 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 196 (Polychromatic418967fa.accept_19_7_18_6_1_3095 7
  18 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 196 2 3 9 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 196 (accept_3_3 5 18
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 196 2 2 9 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 196
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 18 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 196 2 1 9 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 196 (Polychromatic418967fa.accept_19_1_18_6_1_3110 1 18 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 196)))))))))))))))))) (allB_succ 17 196 (allA_of_3_1 17 17 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 196 (allA_succ_of_accept 15 16 196
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 15 16 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 196 2 7 8 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 196 (Polychromatic418967fa.accept_17_13_16_9_1_5128 13 16 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 196 4 3 4 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 196 (accept_3_3 11 16 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 196 2 5 8 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 196 (Polychromatic418967fa.accept_19_9_16_6_1_5774 9 16 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 196 4 2 4 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 196 (Polychromatic418967fa.accept_11_7_5_9_1_884 7
  16 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 196 2 3 8 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 196 (accept_3_3 5 16
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 196 4 1 4 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 196
  (Polychromatic418967fa.accept_19_3_16_6_1_1987 3 16 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 196 2 1 8 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 196 (Polychromatic418967fa.accept_21_1_16_7_1_3763 1 16 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 196)))))))))))))))) (allB_succ 15 196 (allA_succ_of_accept 14 15 196
  (accept_3_3 14 15 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 196
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 15 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 15 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 196 (accept_3_3 11 15 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 15 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 196 (Polychromatic418967fa.accept_10_9_5_6_1_691 9
  15 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 196 (accept_3_3 8 15 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 15 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 196 (accept_3_3 5 15 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  196 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 15 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 15 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 196 (accept_3_3 2 15 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 15 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 196))))))))))))))) (allB_succ 14 196 (allA_of_3_1 14 14 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 196 (allA_succ_of_accept 12 13 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 13 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 196 (accept_3_3 11 13 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 13 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 196 (accept_3_3 8 13 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 196 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 13 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 196 (accept_3_3 5 13 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  196 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 13 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 13 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 196 (accept_3_3 2 13 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 13 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 196))))))))))))) (allB_succ 12 196 (allA_succ_of_accept 11 12
  196 (accept_3_3 11 12 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 196 2 5 6 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 196
  (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 12 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 196 4 2 3 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 196 (Polychromatic418967fa.accept_16_7_12_4_1_1347 7 12 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 196 2 3 6 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 196 (accept_3_3 5 12 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 196 4 1 3 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 196 (Polychromatic418967fa.accept_16_3_12_4_1_170 3 12 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 196 2 1 6 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 12
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 196)))))))))))) (allB_succ 11 196
  (allA_of_3_1 11 11 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 196 (allA_succ_of_accept 9 10 196
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 10 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 196 2 4 5 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 10 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 196 2 3 5 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 196 (accept_3_3 5 10 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 196 2 2 5 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 10 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 196 2 1 5 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 196 (Polychromatic418967fa.accept_11_1_10_9_1_871 1
  10 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 196)))))))))) (allB_succ 9 196
  (allA_succ_of_accept 8 9 196 (accept_3_3 8 9 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 196
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 9 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 9 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 196 (accept_3_3 5 9 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 196 (Polychromatic418967fa.accept_22_4_9_20_1_9823 4 9 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 9
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 196 (accept_3_3 2 9 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 196))))))))) (allB_succ 8 196
  (allA_of_3_1 8 8 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 196 (allA_succ_of_accept 6 7 196
  (Polychromatic418967fa.accept_13_6_7_1_1_335 6 7 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 196 (accept_3_3 5 7 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 196
  (Polychromatic418967fa.accept_18_4_7_16_1_2307 4 7 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 196 (accept_3_3 2 7 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 196 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 7 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 196))))))) (allB_succ 6 196 (allA_succ_of_accept 5 6 196
  (accept_3_3 5 6 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 196 2 2 3 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 6 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 196 2 1 3 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 6 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 196)))))) (allB_succ 5 196 (allA_of_3_1 5 5 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 196 (allA_succ_of_accept 3 4 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 4 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 196 2 1 2 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 196
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 4 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 196)))) (allB_succ 3 196 (allA_succ_of_accept 2 3 196 (accept_3_3 2 3 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 196))) (allB_succ 2 196 (allA_of_3_1 2 2 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


