-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch240_Segment001
-- name    : Polychromatic418967fa_Branch240_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:42:40.463403+00:00
-- url     : https://prove2.me/theorems/12b79789-916b-4092-a99e-477a93f6e961
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch240_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_240_segment_001 : allB 146 240 :=
  allB_succ' 96 145 240 (Eq.refl Bool.true) (allA_succ_of_gcd 95 145 240 5 19 29 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 145 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 94 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 145 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 93 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 145 240 (accept_3_5 92 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 145 240 (Polychromatic418967fa.accept_14_7_5_2_1_2473 91 145 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 145 240 5 18 29 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 145 240 (accept_3_5 89 145 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 145 240 (Polychromatic418967fa.accept_7_4_5_2_1_243
  88 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 145 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 87 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 145 240 (accept_3_5 86 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  145 240 5 17 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 145 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 84 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 145 240 (accept_3_5 83 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 145 240 (Polychromatic418967fa.accept_13_4_2_6_1_1043 82 145 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 145 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 81 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 145 240 5 16 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 145 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 79 145 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 145 240
  (Polychromatic418967fa.accept_21_15_19_9_1_2504 78 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 145 240 (accept_3_5 77 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 145 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 145 240 5 15 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 145 240 (accept_3_5 74 145 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 145 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 73 145 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 240
  (Polychromatic418967fa.accept_17_4_9_2_1_9721 72 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 145 240 (accept_3_5 71 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  145 240 5 14 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 145 240 (Polychromatic418967fa.accept_13_4_2_6_1_1043 69 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 145 240 (accept_3_5 68 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 145 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 145 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 145 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 66
  145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 145 240 5 13 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 145 240
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 64 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 145 240 (Polychromatic418967fa.accept_14_7_5_2_1_2473 63 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 145 240 (accept_3_5 62 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 145 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 145 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 145 240 5 12 29 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 145 240 (accept_3_5 59 145 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 145 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 57 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 240 (accept_3_5 56 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  145 240 5 11 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 145 240 (Polychromatic418967fa.accept_21_12_19_9_1_8442 54 145 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 240 (accept_3_5 53 145 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 145 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 240
  (Polychromatic418967fa.accept_11_7_2_9_1_480 51 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 145 240 5 10 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 145 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 145 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 48
  145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 240 (accept_3_5 47
  145 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 46 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 145 240 5 9 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 145 240 (accept_3_5 44 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 240 (Polychromatic418967fa.accept_25_17_20_15_1_7240 42 145 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 240 (accept_3_5 41 145 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 145 240 5 8 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 145 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 39
  145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 240 (accept_3_5 38
  145 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 240
  (Polychromatic418967fa.accept_11_4_2_9_1_496 37 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 145 240 (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 145 240 5 7 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 145 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 34
  145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 240
  (Polychromatic418967fa.accept_21_12_19_9_1_8442 33 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 145 240 (accept_3_5 32 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 145 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 145 240 5 6 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 145 240 (accept_3_5 29 145 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 240 (Polychromatic418967fa.accept_17_11_9_2_1_8423 28 145 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 240
  (Polychromatic418967fa.accept_13_1_2_6_1_515 27 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 240 (accept_3_5 26 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  145 240 5 5 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 145 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 145 240 (accept_3_5 23 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 145 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 145 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 145 240 5 4 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 145 240
  (Polychromatic418967fa.accept_28_19_5_16_1_14428 19 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 145 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 240 (accept_3_5 17 145 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 145 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 145 240 5 3 29 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 145 240 (accept_3_5 14 145 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 240 (Polychromatic418967fa.accept_9_4_1_6_1_284
  13 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 240 (accept_3_5 11 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  145 240 5 2 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 145 240 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 145 240 (accept_3_5 8 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 145 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 240 (Polychromatic418967fa.accept_22_6_13_20_1_12949 6 145
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 145 240 5 1 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 145 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 145 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 145 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 240 (accept_3_5 2 145 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 145 240 (Polychromatic418967fa.accept_13_1_2_6_1_515 1 145 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 144
  240 (Eq.refl Bool.true) (allA_succ_of_gcd 96 144 240 48 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 144 240 (Polychromatic418967fa.accept_17_10_8_2_1_8411 95 144
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 144 240 2 47 72 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 144 240 3 31 48 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 144 240 4 23 36
  60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 144 240
  (Polychromatic418967fa.accept_21_7_18_9_1_5291 91 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 144 240 6 15 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 144 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 144 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 144 240 8 11 18 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 144 240 3 29 48 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 144 240 2 43 72 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 144 240
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 85 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 144 240 12 7 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 144 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 144 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 144 240 2 41 72 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 144 240 3 27 48 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 144 240 16 5 9 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 144 240
  (Polychromatic418967fa.accept_14_9_4_2_1_983 79 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 240 6 13 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 240 (Polychromatic418967fa.accept_19_1_11_12_1_6112 77 144 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 144 240 4 19 36 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 144 240 3 25 48 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 144 240 2 37 72 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 240
  (Polychromatic418967fa.accept_13_8_1_6_1_997 73 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 240 24 3 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 144 240 (Polychromatic418967fa.accept_21_8_18_9_1_5329 71 144 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 144 240 2 35 72 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 144 240 3 23 48 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 144 240 4 17 36 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 240
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 67 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 240 6 11 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 240 (Polychromatic418967fa.accept_11_10_1_9_1_2060 65 144 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 240 16 4 9 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 144 240 3 21 48 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 144 240 2 31 72 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 61 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 240 12 5 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 240 (Polychromatic418967fa.accept_13_7_1_6_1_3287 59 144 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 240 2 29 72 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 144 240 3 19 48 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 144 240 8 7 18 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 55 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 240 6 9 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 144 240 (Polychromatic418967fa.accept_21_11_18_9_1_465 53 144 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 240 4 13 36 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 144 240 3 17 48 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 144 240 2 25 72 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 240
  (Polychromatic418967fa.accept_21_7_18_9_1_5291 49 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 240 48 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 144 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 144 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 240 2 23 72 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 144 240 3 15 48 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 144 240 4 11 36 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 240
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 240 6 7 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 144 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 144 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 240 8 5 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 144 240 3 13 48 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 144 240 2 19 72 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 240
  (Polychromatic418967fa.accept_14_9_4_2_1_983 37 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 240 12 3 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 240 (Polychromatic418967fa.accept_13_9_1_6_1_510 35 144 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 240 2 17 72 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 144 240 3 11 48 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 144 240 16 2 9 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 240
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 31 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 240 6 5 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 144 240 (Polychromatic418967fa.accept_13_3_1_6_1_509 29 144 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 240 4 7 36 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 144 240 3 9 48 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 144 240 2 13 72 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 240
  (Polychromatic418967fa.accept_21_4_18_9_1_6899 25 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 240 24 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 240 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 144 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 240 2 11 72 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 144 240 3 7 48 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 144 240 4 5 36 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 19
  144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 240 6 3 24 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 240
  (Polychromatic418967fa.accept_21_17_18_9_1_9968 17 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 144 240 16 1 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 144 240 3 5 48 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 144 240 2 7 72 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 144 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 240 12 1 12 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 240
  (Polychromatic418967fa.accept_17_11_8_2_1_3398 11 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 240 2 5 72 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 144 240 3 3 48 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 144 240 8 1 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 144 240 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 144 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 240 6 1 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 5
  144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 240 4 1 36 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 240 3 1 48 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 240 2 1 72 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 240
  (Polychromatic418967fa.accept_19_1_11_12_1_6112 1 144 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 144 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 98 143 240 (Eq.refl Bool.true) (allA_succ_of_accept 97 143 240 (accept_3_4 97 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 143 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 143 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 143 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 95 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 143 240 (accept_3_4 94 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 143 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 93 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 143 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 92 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 143 240 (accept_3_4 91 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 143 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 143 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 143 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 89 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 143 240 (accept_3_4 88 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 143 240 (Polychromatic418967fa.accept_18_15_17_6_1_4043 87 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 143 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 86 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 143 240 (accept_3_4 85 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 143 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 84 143 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 143 240 (accept_3_4 82 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 143 240 (Polychromatic418967fa.accept_17_13_7_2_1_4562 81 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 143 240 (Polychromatic418967fa.accept_17_12_7_2_1_4561 80 143 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 240 (accept_3_4 79 143 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 143 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 143 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 143 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 77 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 143 240 (accept_3_4 76 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 143 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 143 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 74 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 240 (accept_3_4 73 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 240 (Polychromatic418967fa.accept_22_6_11_20_1_12930 72 143 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 143 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 143 240 (accept_3_4 70 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 143 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 143 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 143 240 (accept_3_4 67 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 143 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 143 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 143 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 65 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 143 240 (accept_3_4 64 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 143 240 (Polychromatic418967fa.accept_17_12_7_2_1_4561 63 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 143 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 240 (accept_3_4 61 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 240 (Polychromatic418967fa.accept_17_9_7_2_1_2347 60 143 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 143 240 (accept_3_4 58 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 143 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 143 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 56 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 240 (accept_3_4 55 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 143 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 143 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 240
  (Polychromatic418967fa.accept_22_9_11_20_1_14427 53 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 143 240 (accept_3_4 52 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 143 240 (Polychromatic418967fa.accept_18_15_17_6_1_4043 51 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 50
  143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 240 (accept_3_4 49
  143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 143 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 143 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 240 (accept_3_4 46 143 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 143 240 (Polychromatic418967fa.accept_21_3_17_9_1_9958 45 143 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 240
  (Polychromatic418967fa.accept_19_6_10_12_1_11771 44 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 143 240 (accept_3_4 43 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 143 240 (Polychromatic418967fa.accept_27_15_8_24_1_14426 42 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 240 (Polychromatic418967fa.accept_7_6_3_2_1_461
  41 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 240 (accept_3_4 40
  143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 39 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 143 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 143 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 240 (accept_3_4 37 143 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 143 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 240
  (Polychromatic418967fa.accept_21_14_17_9_1_5326 35 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 143 240 (accept_3_4 34 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 143 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 143 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 143 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 240 (accept_3_4 31 143 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 30
  143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 240 (accept_3_4 28 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 240 (accept_3_4 25 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 240 (Polychromatic418967fa.accept_21_3_17_9_1_9958 24 143 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 240 (accept_3_4 22 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 240 (accept_3_4 19 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 240 (Polychromatic418967fa.accept_21_18_17_9_1_6897 18 143 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 240
  (Polychromatic418967fa.accept_19_17_10_12_1_6157 17 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 143 240 (accept_3_4 16 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 143 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 143 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 143 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 240 (accept_3_4 13 143 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 240 (Polychromatic418967fa.accept_7_5_3_2_1_249
  12 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 240 (accept_3_4 10 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 240 (Polychromatic418967fa.accept_17_9_7_2_1_2347 9 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 240 (accept_3_4 7 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 143 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 240 (accept_3_4 4 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 143 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 240 (accept_3_4 1 143 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  142 240 (Eq.refl Bool.true) (allA_succ_of_gcd 98 142 240 2 49 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 142 240 (Polychromatic418967fa.accept_17_12_6_2_1_2346 97 142
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 142 240 2 48 71 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 142 240 (accept_3_5 95
  142 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 142 240 2 47 71 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 142 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 93 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 142 240 2 46 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 142 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 91 142 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 142 240 2 45 71 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 142 240 (accept_3_5 89 142 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 142 240 2 44 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 142 240
  (Polychromatic418967fa.accept_18_15_16_6_1_1751 87 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 142 240 2 43 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 142 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 85 142 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 142 240 2 42 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 142 240 (accept_3_5 83 142 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 142 240 2 41 71 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 142 240
  (Polychromatic418967fa.accept_17_13_6_2_1_5850 81 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 142 240 2 40 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 142 240 (Polychromatic418967fa.accept_19_3_9_12_1_6253 79 142 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 142 240 2 39 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 142 240 (accept_3_5 77 142 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 142 240 2 38 71 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 142 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 75 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 142 240 2 37 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 142 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 142 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 142 240 2 36 71 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 142 240 (accept_3_5 71 142 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 142 240 2 35 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 142 240 (Polychromatic418967fa.accept_17_1_6_2_1_623
  69 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 240 2 34 71 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 67 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 240 2 33 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 240 (accept_3_5 65 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 240 2 32 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 240 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 142 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 240 2 31 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 240
  (Polychromatic418967fa.accept_22_17_10_20_1_4846 61 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 142 240 2 30 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 142 240 (accept_3_5 59 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 240 2 29 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 142 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 240 2 28 71 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 55 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 240 2 27 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 240 (accept_3_5 53 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 240 2 26 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 240 (Polychromatic418967fa.accept_18_15_16_6_1_1751 51 142 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 240 2 25 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 240 2 24 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 240 (accept_3_5 47 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 240 2 23 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 240 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 142 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 240 2 22 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 240
  (Polychromatic418967fa.accept_19_5_9_12_1_11778 43 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 142 240 2 21 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 142 240 (accept_3_5 41 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 240 2 20 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 142 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 240 2 19 71 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 240 2 18 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 240 (accept_3_5 35 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 240 2 17 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 240 (Polychromatic418967fa.accept_13_7_12_6_1_1039 33 142 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 240 2 16 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 240 2 15 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 240 (accept_3_5 29 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 240 2 14 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 240 (Polychromatic418967fa.accept_21_6_16_9_1_5300 27 142 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 240 2 13 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 240
  (Polychromatic418967fa.accept_21_4_16_9_1_14425 25 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 142 240 2 12 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 142 240 (accept_3_5 23 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 240 2 11 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 142 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 240 2 10 71 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 240 2 9 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 240 (accept_3_5 17 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 240 2 8 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 240 (Polychromatic418967fa.accept_13_2_12_6_1_2394 15 142 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 240 2 7 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 240 2 6 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 240 (accept_3_5 11 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 240 2 5 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 240 (Polychromatic418967fa.accept_25_9_17_15_1_14424 9 142 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 240 2 4 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 240
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 240 2 3 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 240 (accept_3_5 5 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  240 2 2 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 142 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 240 2 1 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 142 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  141 240 (Eq.refl Bool.true) (allA_succ_of_gcd 99 141 240 3 33 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 141 240 (Polychromatic418967fa.accept_21_14_15_9_1_1339 98 141
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 97 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 141 240 3 32 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 141 240 (Polychromatic418967fa.accept_13_4_11_6_1_1033 95 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 141 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 94 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 141 240 3 31 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 141 240 (Polychromatic418967fa.accept_14_8_1_2_1_965 92 141 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 240
  (Polychromatic418967fa.accept_19_15_8_12_1_1286 91 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 141 240 3 30 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 141 240 (Polychromatic418967fa.accept_18_17_15_6_1_1797 89 141 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 141 240
  (Polychromatic418967fa.accept_17_3_5_2_1_14381 88 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 141 240 3 29 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 141 240 (Polychromatic418967fa.accept_13_8_11_6_1_1035 86 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 240
  (Polychromatic418967fa.accept_23_16_3_10_1_14423 85 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 141 240 3 28 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 141 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 141 240
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 82 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 141 240 3 27 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 141 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 80 141 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 240
  (Polychromatic418967fa.accept_21_16_15_9_1_6893 79 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 141 240 3 26 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 141 240 (Polychromatic418967fa.accept_18_5_15_6_1_3999 77 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 76 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 141 240 3 25 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 141 240 (Polychromatic418967fa.accept_21_11_15_9_1_3868 74 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 73 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 141 240 3 24 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 141 240 (Polychromatic418967fa.accept_17_3_5_2_1_14381 71 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 240
  (Polychromatic418967fa.accept_13_5_11_6_1_505 70 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 141 240 3 23 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 141 240 (Polychromatic418967fa.accept_19_11_8_12_1_6204 68 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 240
  (Polychromatic418967fa.accept_17_16_5_2_1_9724 67 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 141 240 3 22 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 141 240 (Polychromatic418967fa.accept_17_14_5_2_1_4559 65 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 240
  (Polychromatic418967fa.accept_14_8_1_2_1_965 64 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 141 240 3 21 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 141 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 141 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 240
  (Polychromatic418967fa.accept_19_4_8_12_1_4757 61 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 141 240 3 20 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 141 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 141 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 240
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 58 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 141 240 3 19 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 141 240 (Polychromatic418967fa.accept_13_4_11_6_1_1033 56 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 141 240 3 18 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 141 240 (Polychromatic418967fa.accept_18_17_15_6_1_1797 53 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 52 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 141 240 3 17 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 141 240 (Polychromatic418967fa.accept_14_8_1_2_1_965 50 141 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 240
  (Polychromatic418967fa.accept_19_11_8_12_1_6204 49 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 141 240 3 16 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 141 240 (Polychromatic418967fa.accept_13_8_11_6_1_1035 47 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 240
  (Polychromatic418967fa.accept_18_10_15_6_1_6621 46 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 141 240 3 15 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 141 240 (Polychromatic418967fa.accept_13_5_11_6_1_505 44 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 240
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 43 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 141 240 3 14 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 141 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 141 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 240
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 40 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 141 240 3 13 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 141 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 141 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 240
  (Polychromatic418967fa.accept_17_3_5_2_1_14381 37 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 141 240 3 12 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 141 240 (Polychromatic418967fa.accept_18_17_15_6_1_1797 35 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 34 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 141 240 3 11 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 141 240 (Polychromatic418967fa.accept_21_11_15_9_1_3868 32 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 141 240 3 10 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 141 240 (Polychromatic418967fa.accept_18_11_15_6_1_2832 29 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 240
  (Polychromatic418967fa.accept_18_10_15_6_1_6621 28 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 141 240 3 9 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 141 240 (Polychromatic418967fa.accept_19_7_8_12_1_9107 26 141 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 240
  (Polychromatic418967fa.accept_19_6_8_12_1_6271 25 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 141 240 3 8 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 141 240 (Polychromatic418967fa.accept_18_5_15_6_1_3999 23 141 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 240 (Polychromatic418967fa.accept_14_8_1_2_1_965 22 141
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 240 3 7 47 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 240 (Polychromatic418967fa.accept_21_19_15_9_1_11533 19 141 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 240 3 6 47 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 240 (Polychromatic418967fa.accept_17_16_5_2_1_9724 16 141 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 141 240 3 5 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 240 (Polychromatic418967fa.accept_17_14_5_2_1_4559
  14 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 141 240 3 4 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 141 240 (Polychromatic418967fa.accept_18_11_15_6_1_2832 11 141 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 240 (Polychromatic418967fa.accept_7_3_1_2_1_247
  10 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 240 3 3 47 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 240
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 8 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 240 (Polychromatic418967fa.accept_19_7_8_12_1_9107 7 141 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 240 3 2 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 240 (Polychromatic418967fa.accept_13_5_11_6_1_505 5 141 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 240
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 4 141 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 141 240 3 1 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 141 240 (Polychromatic418967fa.accept_21_2_15_9_1_3838 2 141 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 240 (Polychromatic418967fa.accept_19_1_8_12_1_6149 1 141
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 140 240 (Eq.refl Bool.true) (allA_succ_of_gcd 100 140 240 20 5 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 140 240 (Polychromatic418967fa.accept_18_9_14_6_1_1790
  99 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 140 240 2 49 70 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 140 240
  (accept_3_4 97 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 140 240 4 24 35 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 140 240 5 19 28 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 140 240 2 47 70
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 140 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 93 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 140 240 4 23 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 140 240 (accept_3_4 91 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 140 240 10 9 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 140 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 89 140 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 140 240 4 22 35 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 140 240
  (Polychromatic418967fa.accept_11_10_8_9_1_492 87 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 140 240 2 43 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 140 240 5 17 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 140 240 4 21 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 140 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 83 140 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 140 240 2 41 70 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 140 240
  (Polychromatic418967fa.accept_13_3_10_6_1_2382 81 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 140 240 20 4 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 140 240 (accept_3_4 79 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78
  140 240 2 39 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 140 240 (Polychromatic418967fa.accept_13_12_10_6_1_3212 77 140 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 140 240 4 19 35 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 140 240 5 15 28 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 140 240 2 37 70 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 140 240 (accept_3_4 73
  140 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 140 240 4 18 35 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 140 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 140 240 10 7 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 140 240 (Polychromatic418967fa.accept_13_4_10_6_1_989 69 140 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 140 240 4 17 35 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 140 240 (accept_3_4 67 140 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 140 240 2 33 70 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 140 240 5 13 28 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 140 240 4 16 35 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 240
  (Polychromatic418967fa.accept_17_12_4_2_1_7116 63 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 140 240 2 31 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 140 240 (accept_3_4 61 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 140 240 20 3 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 140 240 (Polychromatic418967fa.accept_21_17_14_9_1_8456 59 140 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 140 240 2 29 70 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 57 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 140 240 4 14 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 140 240 5 11 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 140 240 2 27 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 140 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 140 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 240 4 13 35 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 240
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 51 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 140 240 10 5 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 140 240 (accept_3_4 49 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 240 4 12 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 140 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 240 2 23 70 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 140 240 5 9 28 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 140 240 4 11 35 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 140 240 (accept_3_4 43 140 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 140 240 2 21 70 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 140 240
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 41 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 140 240 20 2 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 140 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 140 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 140 240 2 19 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 140 240 (accept_3_4 37 140 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 140 240 4 9 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 140 240 5 7 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 140 240 2 17 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 240
  (Polychromatic418967fa.accept_19_14_7_12_1_7732 33 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 140 240 4 8 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 140 240 (accept_3_4 31 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 240 10 3 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 140 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 240 4 7 35 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 240
  (Polychromatic418967fa.accept_18_9_14_6_1_1790 27 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 140 240 2 13 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 140 240 5 5 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 140 240 4 6 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 140 240 (Polychromatic418967fa.accept_17_6_4_2_1_5889 23 140 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 240 2 11 70 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 240 20 1 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 140 240 (accept_3_4 19 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  140 240 2 9 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 140 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 140 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 240 4 4 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 140 240 5 3 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 140 240 2 7 70 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 240 (accept_3_4 13 140 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 240 4 3 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 11
  140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 240 10 1 14 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 240
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 240 4 2 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 140 240 (accept_3_4 7 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140
  240 2 3 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 140
  240 5 1 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 140
  240 4 1 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  140 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 140 240 2 1 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 140 240 (accept_3_4 1 140 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 140 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 102 139 240 (Eq.refl Bool.true) (allA_succ_of_accept 101 139 240 (accept_3_5 101 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 139 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 100 139 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 139 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 99 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 139 240 (accept_3_5 98 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 139 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 97 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 139 240 (Polychromatic418967fa.accept_17_11_3_2_1_5867 96 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 139 240 (accept_3_5 95 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 139 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 94 139 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 139 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 93 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 139 240 (accept_3_5 92 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 139 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 91 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 139 240 (Polychromatic418967fa.accept_11_2_7_9_1_890 90 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 139 240 (accept_3_5 89 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 139 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 88 139 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 139 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 87 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 139 240 (accept_3_5 86 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 139 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 85 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 139 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 84 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 139 240 (accept_3_5 83 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 139 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 82 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 139 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 139 240 (accept_3_5 80 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 139 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 79 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 139 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 139 240 (accept_3_5 77 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 139 240 (Polychromatic418967fa.accept_25_1_14_15_1_14391 76 139 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 139 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 75 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 139 240 (accept_3_5 74 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 139 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 139 240 (Polychromatic418967fa.accept_13_7_9_6_1_148 72 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 240 (accept_3_5 71 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 139 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 139 240
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 69 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 139 240 (accept_3_5 68 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 139 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 139 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 240 (accept_3_5 65 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 240
  (Polychromatic418967fa.accept_18_9_13_6_1_877 63 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 139 240 (accept_3_5 62 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 139 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 139 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 240 (accept_3_5 59 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 240 (Polychromatic418967fa.accept_21_16_13_9_1_2539 58 139 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 240 (accept_3_5 56 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 240 (Polychromatic418967fa.accept_13_2_9_6_1_501 54 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 240 (accept_3_5 53 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 139 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 240
  (Polychromatic418967fa.accept_19_13_6_12_1_6109 51 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 139 240 (accept_3_5 50 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 139 240 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 139 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 139 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 240 (accept_3_5 47 139 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 240 (Polychromatic418967fa.accept_7_4_6_2_1_451
  46 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 240 (accept_3_5 44 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 240 (Polychromatic418967fa.accept_13_3_9_6_1_502 42 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 240 (accept_3_5 41 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 240 (Polychromatic418967fa.accept_13_1_9_6_1_146 40 139
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 240 (accept_3_5 38 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 240 (accept_3_5 35 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 240
  (Polychromatic418967fa.accept_13_7_9_6_1_148 33 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 240 (accept_3_5 32 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 240 (accept_3_5 29 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 240
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 240 (accept_3_5 26 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 240 (accept_3_5 23 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 240 (accept_3_5 20 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 240 (accept_3_5 17 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 240 (accept_3_5 14 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 240 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 240 (accept_3_5 11 139 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 240
  (Polychromatic418967fa.accept_18_9_13_6_1_877 9 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 240 (accept_3_5 8 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 240 (Polychromatic418967fa.accept_21_6_13_9_1_12985 6 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 240 (accept_3_5 5 139 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 139 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 240 (accept_3_5 2 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 139 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 138 240 (Eq.refl Bool.true) (allA_succ_of_gcd 102 138 240 6 17 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 138 240 (Polychromatic418967fa.accept_7_3_5_2_1_17
  101 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 138 240 2 50 69 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 138 240 3 33 46
  80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 138 240 2 49
  69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 138 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 97 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 138 240 6 16 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 138 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 138 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 138 240 2 47 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 138 240 3 31 46 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 138 240 2 46 69 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 138 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 91 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 138 240 6 15 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 89 138 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 138 240 2 44 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 138 240 3 29 46 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 138 240 2 43 69 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 138 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 85 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 240 6 14 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 138 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 138 240 2 41 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 138 240 3 27 46 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 138 240 2 40 69 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 138 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 79 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 240 6 13 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 77 138 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 138 240 2 38 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 138 240 3 25 46 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 138 240 2 37 69 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 138 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 73 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 240 6 12 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 71 138 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 240 2 35 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 138 240 3 23 46 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 138 240 2 34 69 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 240 6 11 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 138 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 240 2 32 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 138 240 3 21 46 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 138 240 2 31 69 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 61 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 240 6 10 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 138 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 240 2 29 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 138 240 3 19 46 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 138 240 2 28 69 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 55 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 240 6 9 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 138 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 138 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 240 2 26 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 138 240 3 17 46 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 138 240 2 25 69 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 240 6 8 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 138 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 138 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 240 2 23 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 138 240 3 15 46 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 138 240 2 22 69 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 240 6 7 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 138 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 138 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 240 2 20 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 138 240 3 13 46 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 138 240 2 19 69 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 240 6 6 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 138 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 138 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 240 2 17 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 138 240 3 11 46 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 138 240 2 16 69 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 240 6 5 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 138 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 138 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 240 2 14 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 138 240 3 9 46 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 138 240 2 13 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 240 6 4 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 138 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 138 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 240 2 11 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 138 240 3 7 46 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 138 240 2 10 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 240 6 3 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 138 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 240 2 8 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 138 240 3 5 46 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 138 240 2 7 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 240 6 2 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 138 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 138 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 240 2 5 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 138 240 3 3 46 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 138 240 2 4 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7
  138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 240 6 1 23 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 138 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 138 240 2 2 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 138 240 3 1 46 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 138 240 2 1 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 138 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 138 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 138
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 137 240 (Eq.refl Bool.true) (allA_succ_of_accept 103 137 240 (accept_3_4 103 137 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 137 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 102 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 137 240
  (Polychromatic418967fa.accept_17_16_1_2_1_3403 101 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 137 240 (accept_3_4 100 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 137 240 (Polychromatic418967fa.accept_21_15_11_9_1_2470 99 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 137 240 (Polychromatic418967fa.accept_9_8_2_6_1_875
  98 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 137 240 (accept_3_4 97
  137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 137 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 96 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 137 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 95 137 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 137 240 (accept_3_4 94 137 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 137 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 93 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 137 240 (Polychromatic418967fa.accept_13_1_7_6_1_142
  92 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 137 240 (accept_3_4 91
  137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 137 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 90 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 137 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 137 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 137 240 (accept_3_4 88 137 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 137 240 (Polychromatic418967fa.accept_13_9_7_6_1_1673 87 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 137 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 86 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 137 240 (accept_3_4 85 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 137 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 137 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 137 240 (accept_3_4 82 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 137 240 (Polychromatic418967fa.accept_17_13_1_2_1_9714 81 137 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 137 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 80 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 137 240 (accept_3_4 79 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 137 240 (Polychromatic418967fa.accept_19_2_4_12_1_13084 78 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 137 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 77 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 137 240 (accept_3_4 76 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 137 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 137 240
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 74 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 137 240 (accept_3_4 73 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 137 240 (Polychromatic418967fa.accept_25_22_12_15_1_14422 72 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 71 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 240 (accept_3_4 70 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 137 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 137 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 137 240 (accept_3_4 67 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 137 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 137 240 (Polychromatic418967fa.accept_14_9_11_2_1_2501 65 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 240 (accept_3_4 64 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 137 240 (Polychromatic418967fa.accept_19_6_4_12_1_6193 63 137
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 62 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 137 240 (accept_3_4 61 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 137 240 (Polychromatic418967fa.accept_21_18_11_9_1_6956 60 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 137 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 240 (accept_3_4 58 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 137 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 240
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 56 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 137 240 (accept_3_4 55 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 137 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 240 (accept_3_4 52 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 240 (Polychromatic418967fa.accept_11_7_5_9_1_884 51 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 137 240 (accept_3_4 49 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 240 (accept_3_4 46 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 240 (Polychromatic418967fa.accept_19_7_4_12_1_4769 45 137 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 240 (accept_3_4 43 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 240 (Polychromatic418967fa.accept_26_16_7_6_1_8941 42 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 240 (accept_3_4 40 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 240
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 38 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 240 (accept_3_4 37 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 240 (Polychromatic418967fa.accept_21_15_11_9_1_2470 36 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 240 (accept_3_4 34 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 240 (accept_3_4 31 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 240 (Polychromatic418967fa.accept_11_7_5_9_1_884 29 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 240 (accept_3_4 28 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 137 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 240 (accept_3_4 25 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 240 (Polychromatic418967fa.accept_19_5_4_12_1_7773 24 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 240 (accept_3_4 22 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 240 (accept_3_4 19 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 240 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 240 (accept_3_4 16 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 240 (Polychromatic418967fa.accept_18_15_11_6_1_4067 15 137 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 240 (accept_3_4 13 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 240 (Polychromatic418967fa.accept_19_11_4_12_1_6106 11 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 240 (accept_3_4 10 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 240 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 137 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 240 (accept_3_4 7 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 240 (accept_3_4 4 137 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 137 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 240
  (Polychromatic418967fa.accept_19_2_4_12_1_13084 2 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 240 (accept_3_4 1 137 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 136 240 (Eq.refl Bool.true) (allA_succ_of_gcd 104 136 240 8 13 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 136 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 103 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 136 240 2 51 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 136 240 (accept_3_5 101 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 136 240 4 25 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 136 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 99 136 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 136 240 2 49 68 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 136 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 97 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 136 240 8 12 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 136 240 (accept_3_5 95 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 136 240 2 47 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 136 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 93 136 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 136 240 4 23 34 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 136 240
  (Polychromatic418967fa.accept_19_15_3_12_1_11789 91 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 136 240 2 45 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 136 240 (accept_3_5 89 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 136 240 8 11 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 136 240 (Polychromatic418967fa.accept_18_15_10_6_1_1781 87 136 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 136 240 2 43 68 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 136 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 85 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 136 240 4 21 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 136 240 (accept_3_5 83 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 136 240 2 41 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 136 240 (Polychromatic418967fa.accept_21_18_10_9_1_5297 81 136 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 136 240 8 10 17 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 136 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 79 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 136 240 2 39 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 136 240 (accept_3_5 77 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 136 240 4 19 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 136 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 136 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 136 240 2 37 68 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 136 240
  (Polychromatic418967fa.accept_23_4_21_10_1_14421 73 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 136 240 8 9 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 136 240 (accept_3_5 71 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 136 240 2 35 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 136 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 136 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 136 240 4 17 34 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 136 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 67 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 136 240 2 33 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 136 240 (accept_3_5 65 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 136 240 8 8 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 136 240 (Polychromatic418967fa.accept_25_13_11_15_1_10998 63 136 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 136 240 2 31 68 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 136 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 61 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 136 240 4 15 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 136 240 (accept_3_5 59 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 136 240 2 29 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 136 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 136 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 136 240 8 7 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 136 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 136 240 2 27 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 136 240 (accept_3_5 53 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 136 240 4 13 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 136 240 (Polychromatic418967fa.accept_18_15_10_6_1_1781 51 136 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 240 2 25 68 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 136 240 8 6 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 136 240 (accept_3_5 47 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  136 240 2 23 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 136 240 (Polychromatic418967fa.accept_19_7_3_12_1_4787 45 136 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 240 4 11 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 43
  136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 136 240 2 21 68 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 136 240 (accept_3_5 41
  136 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 136 240 8 5 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 136 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 136 240 2 19 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 136 240 (Polychromatic418967fa.accept_21_16_10_9_1_9965 37 136 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 136 240 4 9 34 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 136 240 (accept_3_5 35 136 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 136 240 2 17 68 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 136 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 136 240 8 4 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 136 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 136 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 136 240 2 15 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 240 (accept_3_5 29 136 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 240 4 7 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 136 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 240 2 13 68 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 240 8 3 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 136 240 (accept_3_5 23 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  136 240 2 11 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 136 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 136 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 240 4 5 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 19
  136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 136 240 2 9 68 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 136 240 (accept_3_5 17
  136 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 136 240 8 2 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 136 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 136 240 2 7 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 136 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 136 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 240 4 3 34 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 240 (accept_3_5 11 136 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 240 2 5 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 240 (Polychromatic418967fa.accept_19_9_3_12_1_6191
  9 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 136 240 8 1 17 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 136 240 2 3 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 136 240 (accept_3_5 5 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136
  240 4 1 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  136 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 136 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 136 240 2 1 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 136 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 136 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 135 240 (Eq.refl Bool.true) (allA_succ_of_gcd 105 135 240 15 7 9 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 135 240
  (Polychromatic418967fa.accept_18_14_9_6_1_1777 104 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 135 240 (Polychromatic418967fa.accept_13_12_5_6_1_1050 103 135 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 135 240 3 34 45 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 135 240
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 101 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 135 240 5 20 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 99 135 240 3 33 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 135 240 (Polychromatic418967fa.accept_18_8_9_6_1_3989 98 135
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 240
  (Polychromatic418967fa.accept_18_7_9_6_1_4023 97 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 135 240 3 32 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 95 135 240 5 19 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 94 135 240 (Polychromatic418967fa.accept_11_6_3_9_1_906 94 135 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 135 240 3 31 45 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 135 240
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 92 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 135 240 (Polychromatic418967fa.accept_14_7_9_2_1_2489 91 135 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 135 240 15 6 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 135 240 (Polychromatic418967fa.accept_13_11_5_6_1_519
  89 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 240
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 88 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 135 240 3 29 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 135 240 (Polychromatic418967fa.accept_17_1_16_2_1_1404 86 135 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 135 240 5 17 27 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 135 240 3 28 45 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 135 240
  (Polychromatic418967fa.accept_11_6_3_9_1_906 83 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 135 240 (Polychromatic418967fa.accept_13_4_5_6_1_3201 82 135 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 135 240 3 27 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 135 240 5 16 27 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 135 240
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 79 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 135 240 3 26 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 135 240 (Polychromatic418967fa.accept_13_12_5_6_1_1050 77 135 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 240
  (Polychromatic418967fa.accept_13_11_5_6_1_519 76 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 135 240 15 5 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 135 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 74 135 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 240 (Polychromatic418967fa.accept_17_5_16_2_1_7094 73 135
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 135 240 3 24 45 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 135 240
  (Polychromatic418967fa.accept_19_14_2_12_1_13164 71 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 135 240 5 14 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 69 135 240 3 23 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 135 240 (Polychromatic418967fa.accept_13_3_5_6_1_3192 68 135
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 240
  (Polychromatic418967fa.accept_14_11_9_2_1_6382 67 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 135 240 3 22 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 135 240 5 13 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 135 240 (Polychromatic418967fa.accept_13_12_5_6_1_1050 64 135 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 135 240 3 21 45 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 135 240
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 62 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 240 (Polychromatic418967fa.accept_11_6_3_9_1_906 61 135 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 240 15 4 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 240
  (Polychromatic418967fa.accept_17_8_16_2_1_10847 59 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 135 240 (Polychromatic418967fa.accept_19_1_2_12_1_7725 58 135 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 135 240 3 19 45 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 135 240
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 56 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 135 240 5 11 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 135 240 3 18 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 135 240 (Polychromatic418967fa.accept_13_1_5_6_1_1048 53 135 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 240
  (Polychromatic418967fa.accept_17_1_16_2_1_1404 52 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 135 240 3 17 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 135 240 5 10 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 135 240 (Polychromatic418967fa.accept_13_10_5_6_1_1671 49 135 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 135 240 3 16 45 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 135 240
  (Polychromatic418967fa.accept_19_9_2_12_1_6243 47 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 46 135 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 240 15 3 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 240 (Polychromatic418967fa.accept_18_8_9_6_1_3989
  44 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 240
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 43 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 135 240 3 14 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 135 240 (Polychromatic418967fa.accept_19_3_2_12_1_13118 41 135 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 135 240 5 8 27 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 135 240 3 13 45 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 135 240
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 38 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 240 (Polychromatic418967fa.accept_13_11_5_6_1_519 37 135 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 135 240 3 12 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 135 240 5 7 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 135 240
  (Polychromatic418967fa.accept_23_11_20_10_1_9664 34 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 135 240 3 11 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 135 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 32 135 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 240
  (Polychromatic418967fa.accept_17_14_16_2_1_4553 31 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 135 240 15 2 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 135 240 (Polychromatic418967fa.accept_13_3_5_6_1_3192 29 135 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 240
  (Polychromatic418967fa.accept_11_6_3_9_1_906 28 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 135 240 3 9 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 135 240 (Polychromatic418967fa.accept_18_8_9_6_1_3989 26 135 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 135 240 5 5 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 135 240 3 8 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 240 (Polychromatic418967fa.accept_13_10_5_6_1_1671
  23 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 240
  (Polychromatic418967fa.accept_17_5_16_2_1_7094 22 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 135 240 3 7 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 135 240 5 4 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 135 240 (Polychromatic418967fa.accept_18_1_9_6_1_6630 19 135 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 240 3 6 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 240 (Polychromatic418967fa.accept_11_6_3_9_1_906
  17 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 240
  (Polychromatic418967fa.accept_13_3_5_6_1_3192 16 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 135 240 15 1 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 135 240 (Polychromatic418967fa.accept_13_1_5_6_1_1048 14 135 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 240 (Polychromatic418967fa.accept_18_13_9_6_1_4024 13 135
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 240 3 4 45 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 240
  (Polychromatic418967fa.accept_13_11_5_6_1_519 11 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 135 240 5 2 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 135 240 3 3 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 135 240 (Polychromatic418967fa.accept_17_8_16_2_1_10847 8 135 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 240 (Polychromatic418967fa.accept_14_7_9_2_1_2489 7 135 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 240 3 2 45 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 135 240 5 1 27 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 240
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 4 135 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 135 240 3 1 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 135 240 (Polychromatic418967fa.accept_18_2_9_6_1_4025 2 135 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 240 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 135 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 134 240 (Eq.refl Bool.true) (allA_succ_of_gcd 106 134 240 2 53 67 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 134 240
  (Polychromatic418967fa.accept_23_13_19_10_1_14319 105 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 134 240 2 52 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 134 240 (accept_3_4 103 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 134 240 2 51 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 134 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 101 134 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 134 240 2 50 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 134 240
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 99 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 134 240 2 49 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 134 240 (accept_3_4 97 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 134 240 2 48 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 134 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 95 134 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 134 240 2 47 67 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 134 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 93 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 134 240 2 46 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 134 240 (accept_3_4 91 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 134 240 2 45 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 134 240 (Polychromatic418967fa.accept_13_11_4_6_1_1006 89 134 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 134 240 2 44 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 134 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 87 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 134 240 2 43 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 134 240 (accept_3_4 85 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 134 240 2 42 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 134 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 134 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 134 240 2 41 67 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 134 240
  (Polychromatic418967fa.accept_11_4_2_9_1_496 81 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 134 240 2 40 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 134 240 (accept_3_4 79 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 134 240 2 39 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 134 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 77 134 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 134 240 2 38 67 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 75 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 134 240 2 37 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 134 240 (accept_3_4 73 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 134 240 2 36 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 240 (Polychromatic418967fa.accept_14_1_8_2_1_1675 71 134 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 240 2 35 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 134 240 2 34 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 134 240 (accept_3_4 67 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 240 2 33 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 65 134 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 240 2 32 67 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 240
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 63 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 134 240 2 31 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 134 240 (accept_3_4 61 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 240 2 30 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 134 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 240 2 29 67 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 57 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 134 240 2 28 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 134 240 (accept_3_4 55 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 240 2 27 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 240 (Polychromatic418967fa.accept_25_3_9_15_1_14420 53 134 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 240 2 26 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 240
  (Polychromatic418967fa.accept_11_7_2_9_1_480 51 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 240 2 25 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 240 (accept_3_4 49 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 240 2 24 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 134 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 240 2 23 67 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 240 2 22 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 240 (accept_3_4 43 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 240 2 21 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 134 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 240 2 20 67 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 39 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 240 2 19 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 240 (accept_3_4 37 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 240 2 18 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 240 (Polychromatic418967fa.accept_13_9_4_6_1_1005 35 134 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 240 2 17 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 240
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 33 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 240 2 16 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 240 (accept_3_4 31 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 240 2 15 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 134 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 240 2 14 67 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 240 2 13 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 240 (accept_3_4 25 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 240 2 12 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 134 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 240 2 11 67 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 240 2 10 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 240 (accept_3_4 19 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 240 2 9 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 134 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 240 2 8 67 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 240
  (Polychromatic418967fa.accept_11_4_2_9_1_496 15 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 134 240 2 7 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 134 240 (accept_3_4 13 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 240 2 6 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 134 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 240 2 5 67 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 240
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 240 2 4 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 240 (accept_3_4 7 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  240 2 3 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 134 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 240 2 2 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 134 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 240 2 1 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 240 (accept_3_4 1 134 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 133 240 (Eq.refl Bool.true) (allA_succ_of_accept 107 133 240 (accept_3_5 107 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 133 240 (Polychromatic418967fa.accept_22_18_1_20_1_12931 106
  133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 133 240
  (Polychromatic418967fa.accept_13_1_3_6_1_158 105 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 133 240 (accept_3_5 104 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 133 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 103 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 133 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 102 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 133 240 (accept_3_5 101 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 133 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 100 133
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 133 240
  (Polychromatic418967fa.accept_18_9_7_6_1_5331 99 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 133 240 (accept_3_5 98 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 133 240 (Polychromatic418967fa.accept_21_13_7_9_1_2528 97 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 133 240 (Polychromatic418967fa.accept_13_5_3_6_1_3278 96 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 133 240 (accept_3_5 95 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 133 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 94 133 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 133 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 93 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 133 240 (accept_3_5 92 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 133 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 91 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 133 240 (Polychromatic418967fa.accept_17_5_14_2_1_4568 90 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 240 (accept_3_5 89 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 240 (Polychromatic418967fa.accept_13_10_3_6_1_1003 88 133
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 133 240
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 87 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 133 240 (accept_3_5 86 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 133 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 85 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 133 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 84 133 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 133 240 (accept_3_5 83 133 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 133 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 82 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 133 240
  (Polychromatic418967fa.accept_18_9_7_6_1_5331 81 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 133 240 (accept_3_5 80 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 133 240 (Polychromatic418967fa.accept_13_1_3_6_1_158 79 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 133 240 (Polychromatic418967fa.accept_21_15_7_9_1_11550 78 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 133 240 (accept_3_5 77 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 133 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 76 133 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 75 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 133 240 (accept_3_5 74 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 133 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 133 240 (Polychromatic418967fa.accept_23_3_18_10_1_14419 72 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 240 (accept_3_5 71 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 133 240 (Polychromatic418967fa.accept_13_5_3_6_1_3278 70 133
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 240
  (Polychromatic418967fa.accept_21_6_7_9_1_5288 69 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 133 240 (accept_3_5 68 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 133 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 133 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 66 133 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 240 (accept_3_5 65 133 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 64 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 240
  (Polychromatic418967fa.accept_18_9_7_6_1_5331 63 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 133 240 (accept_3_5 62 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 240 (Polychromatic418967fa.accept_13_9_3_6_1_1661 61 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 240 (Polychromatic418967fa.accept_21_18_7_9_1_2529 60 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 240 (accept_3_5 59 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 133 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 240 (accept_3_5 56 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 240 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 240 (accept_3_5 53 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 240 (Polychromatic418967fa.accept_21_10_7_9_1_11527 52 133
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 240
  (Polychromatic418967fa.accept_14_9_7_2_1_2483 51 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 240 (accept_3_5 50 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 133 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 240 (accept_3_5 47 133 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 240
  (Polychromatic418967fa.accept_18_9_7_6_1_5331 45 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 240 (accept_3_5 44 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 240 (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 240 (Polychromatic418967fa.accept_25_17_8_15_1_14418 42 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 240 (accept_3_5 41 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 133 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 240 (accept_3_5 38 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 240 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 240 (accept_3_5 35 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 240 (Polychromatic418967fa.accept_21_13_7_9_1_2528 34 133
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 240
  (Polychromatic418967fa.accept_14_5_7_2_1_468 33 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 240 (accept_3_5 32 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 133 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 240 (accept_3_5 29 133 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 240
  (Polychromatic418967fa.accept_13_1_3_6_1_158 27 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 240 (accept_3_5 26 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 240 (Polychromatic418967fa.accept_22_3_1_20_1_2059 25 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 240 (Polychromatic418967fa.accept_21_3_7_9_1_8519 24 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 240 (accept_3_5 23 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 133 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 240 (accept_3_5 20 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 240 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 240 (accept_3_5 17 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 240 (Polychromatic418967fa.accept_17_16_14_2_1_5841 16 133
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 240
  (Polychromatic418967fa.accept_21_15_7_9_1_11550 15 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 133 240 (accept_3_5 14 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 133 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 133 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 133 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 240 (accept_3_5 11 133 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 10
  133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 240
  (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 240 (accept_3_5 8 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 240 (Polychromatic418967fa.accept_25_7_8_15_1_14417 7 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 240 (Polychromatic418967fa.accept_21_6_7_9_1_5288 6 133 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 240 (accept_3_5 5 133 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 133 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 240 (accept_3_5 2 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 133 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 132 240 (Eq.refl Bool.true) (allA_succ_of_gcd 108 132 240 12 9 11 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 132 240
  (Polychromatic418967fa.accept_21_2_6_9_1_5355 107 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 132 240 2 53 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 132 240 3 35 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 132 240 4 26 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 132 240 (Polychromatic418967fa.accept_13_12_2_6_1_2396 103 132
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 132 240 6 17 22 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 132 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 101 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 132 240 4 25 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 132 240 3 33 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 132 240 2 49 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 240 (Polychromatic418967fa.accept_21_13_6_9_1_1328 97 132
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 132 240 12 8 11 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 132 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 95 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 132 240 2 47 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 132 240 3 31 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 132 240 4 23 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 240 (Polychromatic418967fa.accept_17_6_13_2_1_4549 91 132
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 132 240 6 15 22 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 132 240
  (Polychromatic418967fa.accept_19_13_18_12_1_3428 89 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 132 240 4 22 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 132 240 3 29 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 132 240 2 43 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 132 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 85
  132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 132 240 12 7 11 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 132 240
  (Polychromatic418967fa.accept_17_15_13_2_1_3418 83 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 132 240 2 41 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 81 132 240 3 27 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 132 240 4 20 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 132 240 (Polychromatic418967fa.accept_13_1_2_6_1_515
  79 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 132 240 6 13 22 40
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 132 240
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 77 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 132 240 4 19 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 132 240 3 25 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 132 240 2 37 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 132 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 132 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 132 240 12 6 11 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 132 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 132 240 2 35 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 132 240 3 23 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 132 240 4 17 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 132 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 132 240 6 11 22 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 132 240
  (Polychromatic418967fa.accept_21_2_6_9_1_5355 65 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 132 240 4 16 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 132 240 3 21 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 132 240 2 31 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 240 (Polychromatic418967fa.accept_13_9_2_6_1_514 61 132 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 132 240 12 5 11 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 132 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 132 240 2 29 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 132 240 3 19 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 132 240 4 14 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 132 240 (Polychromatic418967fa.accept_19_17_18_12_1_4783 55 132
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 132 240 6 9 22 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 132 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 132 240 4 13 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 132 240 3 17 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 132 240 2 25 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 240 (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 132
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 132 240 12 4 11 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 132 240
  (Polychromatic418967fa.accept_13_8_2_6_1_2385 47 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 240 2 23 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 132 240 3 15 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 132 240 4 11 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 132 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 132 240 6 7 22 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 132 240
  (Polychromatic418967fa.accept_17_7_13_2_1_10840 41 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 132 240 4 10 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 132 240 3 13 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 132 240 2 19 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 240 (Polychromatic418967fa.accept_21_16_6_9_1_8464
  37 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 132 240 12 3 11 20
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 132 240
  (Polychromatic418967fa.accept_13_9_2_6_1_514 35 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 132 240 2 17 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 132 240 3 11 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 240 4 8 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 132 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 132 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 240 6 5 22 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 240 4 7 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 132 240 3 9 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 132 240 2 13 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 132 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 132 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 240 12 2 11 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 240
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 23 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 132 240 2 11 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 132 240 3 7 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 132 240 4 5 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 132 240 (Polychromatic418967fa.accept_25_19_7_15_1_14416 19 132 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 240 6 3 22 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 132 240 4 4 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 132 240 3 5 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 132 240 2 7 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 132 240 (Polychromatic418967fa.accept_19_13_18_12_1_3428 13 132 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 240 12 1 11 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 240 2 5 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 132 240 3 3 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 132 240 4 2 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 132 240 (Polychromatic418967fa.accept_17_7_13_2_1_10840 7 132 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 240 6 1 22 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 240
  (Polychromatic418967fa.accept_23_5_17_10_1_11273 5 132 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 240 4 1 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 132 240 3 1 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 2 132 240 2 1 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 132 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 132 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 131 240 (Eq.refl Bool.true) (allA_succ_of_accept 109 131 240 (accept_3_4 109 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 131 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 108 131
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 131 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 107 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 131 240 (accept_3_4 106 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 131 240 (Polychromatic418967fa.accept_14_7_5_2_1_2473 105 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 131 240 (Polychromatic418967fa.accept_22_16_21_20_1_11359 104 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 131 240 (accept_3_4 103 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 131 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 102 131
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 131 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 101 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 131 240 (accept_3_4 100 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 131 240 (Polychromatic418967fa.accept_13_8_1_6_1_997 99 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 131 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 98 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 131 240 (accept_3_4 97 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 131 240 (Polychromatic418967fa.accept_11_8_10_9_1_1401 96 131 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 131 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 95 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 131 240 (accept_3_4 94 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 131 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 93 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 131 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 92 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 131 240 (accept_3_4 91 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 131 240 (Polychromatic418967fa.accept_19_14_17_12_1_6099 90 131 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 131 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 89 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 131 240 (accept_3_4 88 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 131 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 131 240 (Polychromatic418967fa.accept_13_8_1_6_1_997 86 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 131 240 (accept_3_4 85 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 131 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 131 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 131 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 83 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 131 240 (accept_3_4 82 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 131 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 131 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 131 240 (accept_3_4 79 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 131 240 (Polychromatic418967fa.accept_11_1_10_9_1_871 78 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 240
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 77 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 131 240 (accept_3_4 76 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 131 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 131 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 240 (accept_3_4 73 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 240 (Polychromatic418967fa.accept_13_7_1_6_1_3287 72 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 131 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 131 240 (accept_3_4 70 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 131 240 (Polychromatic418967fa.accept_18_15_5_6_1_5293 69 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 131 240 (Polychromatic418967fa.accept_13_3_1_6_1_509 68 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 240 (accept_3_4 67 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 131 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 131 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 131 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 131 240 (accept_3_4 64 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 131 240 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 131 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 62 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 240 (accept_3_4 61 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 131 240 (accept_3_4 58 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 131 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 131 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 56 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 240 (accept_3_4 55 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 240 (Polychromatic418967fa.accept_13_2_1_6_1_2365 54 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 240 (accept_3_4 52 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 240 (Polychromatic418967fa.accept_18_15_5_6_1_5293 51 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 240 (Polychromatic418967fa.accept_23_4_16_10_1_9573 50 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 240 (accept_3_4 49 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 131 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 240 (accept_3_4 46 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 44 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 240 (accept_3_4 43 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 240 (Polychromatic418967fa.accept_13_3_1_6_1_509 42 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 240
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 240 (accept_3_4 40 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 240 (accept_3_4 37 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 240 (Polychromatic418967fa.accept_21_15_5_9_1_5315 36 131 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 240 (accept_3_4 34 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 240 (Polychromatic418967fa.accept_13_7_1_6_1_3287 33 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 240 (accept_3_4 31 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 240 (accept_3_4 28 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 240 (Polychromatic418967fa.accept_17_10_12_2_1_3385 27 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 240 (accept_3_4 25 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 240
  (Polychromatic418967fa.accept_11_1_10_9_1_871 23 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 240 (accept_3_4 22 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 240 (accept_3_4 19 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 240 (accept_3_4 16 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 240 (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 240 (Polychromatic418967fa.accept_19_14_17_12_1_6099 14 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 240 (accept_3_4 13 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 131 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 240 (accept_3_4 10 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 240 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 240 (accept_3_4 7 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 240 (Polychromatic418967fa.accept_17_6_12_2_1_10966 6 131 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 240
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 240 (accept_3_4 4 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 131 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 240 (accept_3_4 1 131 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 130 240 (Eq.refl Bool.true) (allA_succ_of_gcd 110 130 240 10 11 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 130 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 109 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 130 240 2 54 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 130 240 (accept_3_5 107 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 130 240 2 53 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 130 240 5 21 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 130 240 2 52 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 130 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 103 130
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 130 240 2 51 65 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 130 240 (accept_3_5
  101 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 130 240 10 10 13 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 130 240
  (Polychromatic418967fa.accept_19_4_16_12_1_485 99 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 130 240 2 49 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 130 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 97 130 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 130 240 2 48 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 130 240 5 19 26 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 130 240 2 47 65 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 130 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 93 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 130 240 2 46 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 130 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 91 130 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 130 240 10 9 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 130 240 (accept_3_5 89 130 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 130 240 2 44 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 130 240 (Polychromatic418967fa.accept_18_15_4_6_1_1763
  87 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 130 240 2 43 65 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 130 240 5 17 26
  48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 130 240 2 42
  65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 130 240
  (accept_3_5 83 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 130 240 2 41 65 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 130 240
  (Polychromatic418967fa.accept_19_5_16_12_1_6175 81 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 130 240 10 8 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 130 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 79 130 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 130 240 2 39 65 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 130 240 (accept_3_5 77 130 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 130 240 2 38 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 130 240 5 15 26 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 130 240 2 37 65 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 130 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 73 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 130 240 2 36 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 130 240 (accept_3_5 71 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 130 240 10 7 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 130 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 130 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 130 240 2 34 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 130 240
  (Polychromatic418967fa.accept_27_13_22_24_1_14415 67 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 130 240 2 33 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 65 130 240 5 13 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 130 240 2 32 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 130 240
  (Polychromatic418967fa.accept_19_6_16_12_1_6118 63 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 130 240 2 31 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 130 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 130 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 130 240 10 6 13 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 130 240 (accept_3_5 59 130 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 130 240 2 29 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 130 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 130 240 2 28 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 130 240 5 11 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 130 240 2 27 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 130 240 (accept_3_5 53 130 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 130 240 2 26 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 130 240 (Polychromatic418967fa.accept_14_9_4_2_1_983 51 130 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 240 10 5 13 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 240
  (Polychromatic418967fa.accept_25_24_5_15_1_14414 49 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 130 240 2 24 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 130 240 (accept_3_5 47 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 240 2 23 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 130 240 5 9 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 130 240 2 22 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 130 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 130 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 130 240 2 21 65 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 130 240 (accept_3_5 41 130 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 130 240 10 4 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 130 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 130 240 2 19 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 130 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 130 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 130 240 2 18 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 130 240 5 7 26 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 130 240 2 17 65 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 130 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 130 240 2 16 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 130 240 (Polychromatic418967fa.accept_23_8_15_10_1_11259 31 130 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 130 240 10 3 13 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 130 240 (accept_3_5 29 130 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 130 240 2 14 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 130 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 130 240 2 13 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 130 240 5 5 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 130 240 2 12 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 130 240 (accept_3_5 23 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 240 2 11 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 130 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 240 10 2 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 240 2 9 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 130 240 (accept_3_5 17 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 130 240 2 8 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 130 240 5 3 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 130 240 2 7 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 130 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 240 2 6 65 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 240 (accept_3_5 11 130 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 240 10 1 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 240
  (Polychromatic418967fa.accept_14_9_4_2_1_983 9 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 240 2 4 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 130 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 240 2 3 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 130 240 5 1 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 130 240 2 2 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 130 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 240 2 1 65 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 130 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 130
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 129 240 (Eq.refl Bool.true) (allA_succ_of_gcd 111 129 240 3 37 43 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 129 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 110 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 129 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 109 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 129 240 3 36 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 129 240 (Polychromatic418967fa.accept_9_8_3_6_1_533
  107 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 129 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 106 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 129 240 3 35 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 129 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 104 129 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 103 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 129 240 3 34 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 129 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 101 129 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 129 240 (Polychromatic418967fa.accept_9_1_3_6_1_70
  100 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 129 240 3 33 43 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 129 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 98 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 129 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 97 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 129 240 3 32 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 129 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 95
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 129 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 94 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 129 240 3 31 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 129 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 92 129 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 91
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 129 240 3 30 43 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 129 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 89 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 129 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 88 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 129 240 3 29 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 129 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 86
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 85 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 129 240 3 28 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 129 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 129 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 240 (Polychromatic418967fa.accept_7_5_3_2_1_249
  82 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 129 240 3 27 43 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 129 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 80 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 129 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 129 240 3 26 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 129 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 77
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 76 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 129 240 3 25 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 129 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 129 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 73
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 129 240 3 24 43 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 129 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 129 240 3 23 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 129 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 68
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 129 240 3 22 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 129 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 129 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 64
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 129 240 3 21 43 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 129 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 129 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 129 240 3 20 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 129 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 129 240 3 19 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 129 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 129 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 240 (Polychromatic418967fa.accept_7_6_3_2_1_461
  55 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 129 240 3 18 43 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 129 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 129 240 3 17 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 129 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 50
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 129 240 3 16 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 129 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 129 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 46
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 129 240 3 15 43 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 129 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 129 240 3 14 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 129 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 41
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 129 240 3 13 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 129 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 129 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 129 240 3 12 43 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 129 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 129 240 3 11 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 129 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 129 240 3 10 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 129 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 129 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 129 240 3 9 43 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 129 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 240 3 8 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 23
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 22 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 129 240 3 7 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 129 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 129 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 240 3 6 43 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 240 3 5 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 129 240 3 4 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 129 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 129 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 240 3 3 43 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 240 3 2 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 129 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 129 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 129 240 3 1 43 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 129 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 129 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 129 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 128 240 (Eq.refl Bool.true) (allA_succ_of_gcd 112 128 240 16 7 8 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 128 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 111 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 128 240 2 55 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 128 240 (accept_3_4 109 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 128 240 4 27 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 128 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 107 128 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 128 240 2 53 64 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 128 240
  (Polychromatic418967fa.accept_19_10_14_12_1_4795 105 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 128 240 8 13 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 128 240 (accept_3_4 103 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 128 240 2 51 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 128 240 (Polychromatic418967fa.accept_11_2_7_9_1_890 101 128 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 128 240 4 25 32 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 128 240
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 99 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 128 240 2 49 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 128 240 (accept_3_4 97 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 128 240 16 6 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 128 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 95 128 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 128 240 2 47 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 128 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 93
  128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 128 240 4 23 32 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 128 240 (accept_3_4 91
  128 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 128 240 2 45 64 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 128 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 89 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 128 240 8 11 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 128 240 (Polychromatic418967fa.accept_21_3_2_9_1_5338 87 128 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 128 240 2 43 64 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 128 240 (accept_3_4 85 128 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 128 240 4 21 32 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 128 240
  (Polychromatic418967fa.accept_13_5_11_6_1_505 83 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 128 240 2 41 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 128 240 (Polychromatic418967fa.accept_18_9_2_6_1_9322 81 128 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 128 240 16 5 8 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 128 240 (accept_3_4 79 128 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 128 240 2 39 64 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 128 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 77 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 128 240 4 19 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 128 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 128 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 128 240 2 37 64 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 128 240 (accept_3_4 73 128 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 128 240 8 9 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 128 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 71
  128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 128 240 2 35 64 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 128 240
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 69 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 128 240 4 17 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 128 240 (accept_3_4 67 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 128 240 2 33 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 128 240 (Polychromatic418967fa.accept_23_19_13_10_1_11249 65 128 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 240 16 4 8 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 240
  (Polychromatic418967fa.accept_18_9_2_6_1_9322 63 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 128 240 2 31 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 128 240 (accept_3_4 61 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 240 4 15 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 128 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 240 2 29 64 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 57 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 240 8 7 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 128 240 (accept_3_4 55 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  128 240 2 27 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 128 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 128 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 240 4 13 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 240
  (Polychromatic418967fa.accept_19_13_14_12_1_4797 51 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 128 240 2 25 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 128 240 (accept_3_4 49 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 240 16 3 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 128 240 (Polychromatic418967fa.accept_13_8_11_6_1_1035 47 128 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 240 2 23 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 240 (Polychromatic418967fa.accept_17_11_9_2_1_8423
  45 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 128 240 4 11 32 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 128 240
  (accept_3_4 43 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 128 240 2 21 64 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 128 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 128 240 8 5 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 128 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 128 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 128 240 2 19 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 128 240 (accept_3_4 37 128 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 128 240 4 9 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 128 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 128 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 240 2 17 64 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 240
  (Polychromatic418967fa.accept_21_12_2_9_1_6866 33 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 128 240 16 2 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 128 240 (accept_3_4 31 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  128 240 2 15 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 128 240 (Polychromatic418967fa.accept_19_10_14_12_1_4795 29 128 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 240 4 7 32 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 240
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 240 2 13 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 240 (accept_3_4 25 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 240 8 3 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 128 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 128 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 240 2 11 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 21
  128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 128 240 4 5 32 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 128 240 (accept_3_4 19
  128 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 128 240 2 9 64 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 128 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 128 240 16 1 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 128 240 (Polychromatic418967fa.accept_21_15_2_9_1_9962 15 128 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 240 2 7 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 240 (accept_3_4 13 128 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 240 4 3 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 240 (Polychromatic418967fa.accept_17_11_9_2_1_8423 11 128
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 240 2 5 64 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 240
  (Polychromatic418967fa.accept_18_9_2_6_1_9322 9 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 128 240 8 1 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 128 240 (accept_3_4 7 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128
  240 2 3 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  128 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 128 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 128 240 4 1 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 128 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 128 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 240 2 1 64 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 240 (accept_3_4 1 128 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 128
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 127 240 (Eq.refl Bool.true) (allA_succ_of_accept 113 127 240 (accept_3_5 113 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 127 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 112 127
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 127 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 111 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 127 240 (accept_3_5 110 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 127 240 (Polychromatic418967fa.accept_13_5_10_6_1_2361 109 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 127 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 108 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 127 240 (accept_3_5 107 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 127 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 106 127
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 127 240
  (Polychromatic418967fa.accept_23_13_12_10_1_7931 105 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 127 240 (accept_3_5 104 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 127 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 103 127 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 127 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 102 127
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 127 240 (accept_3_5 101 127
  240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 127 240
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 100 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 127 240 (Polychromatic418967fa.accept_18_9_1_6_1_5301 99 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 127 240 (accept_3_5 98 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 127 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 97 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 127 240
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 96 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 127 240 (accept_3_5 95 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 127 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 94 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 127 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 93 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 127 240 (accept_3_5 92 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 127 240 (Polychromatic418967fa.accept_11_3_6_9_1_1378 91 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 127 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 90 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 127 240 (accept_3_5 89 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 127 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 88 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 127 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 127 240 (accept_3_5 86 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 127 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 85 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 127 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 84 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 127 240 (accept_3_5 83 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 127 240 (Polychromatic418967fa.accept_13_4_10_6_1_989 82 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 127 240 (Polychromatic418967fa.accept_13_3_10_6_1_2382 81 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 127 240 (accept_3_5 80 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 127 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 79 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 127 240
  (Polychromatic418967fa.accept_14_8_1_2_1_965 78 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 127 240 (accept_3_5 77 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 127 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 127 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 75 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 127 240 (accept_3_5 74 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 127 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 73 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 127 240
  (Polychromatic418967fa.accept_27_18_19_24_1_14413 72 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 127 240 (accept_3_5 71 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 127 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 127 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 127 240 (accept_3_5 68 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 127 240 (Polychromatic418967fa.accept_9_4_1_6_1_284
  67 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 127 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 66 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 127 240 (accept_3_5 65 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 127 240 (Polychromatic418967fa.accept_13_12_10_6_1_3212 64 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 127 240 (Polychromatic418967fa.accept_18_9_1_6_1_5301 63 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 127 240 (accept_3_5 62 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 127 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 240
  (Polychromatic418967fa.accept_19_3_13_12_1_10525 60 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 127 240 (accept_3_5 59 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 127 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 127 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 240 (accept_3_5 56 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 127 240 (Polychromatic418967fa.accept_7_6_1_2_1_230
  55 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 240
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 54 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 240 (accept_3_5 53 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 240 (Polychromatic418967fa.accept_13_12_10_6_1_3212 51 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 240 (accept_3_5 50 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 240 (accept_3_5 47 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 240 (Polychromatic418967fa.accept_25_21_2_15_1_14412 46 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 240 (accept_3_5 44 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 240
  (Polychromatic418967fa.accept_13_3_10_6_1_2382 42 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 240 (accept_3_5 41 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 240 (accept_3_5 38 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 240 (Polychromatic418967fa.accept_19_18_13_12_1_4775 37 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 240
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 240 (accept_3_5 35 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 240 (Polychromatic418967fa.accept_17_16_8_2_1_5890 33 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 240 (accept_3_5 32 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 240 (accept_3_5 29 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 240 (Polychromatic418967fa.accept_13_2_10_6_1_1676 28 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 240 (accept_3_5 26 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 240 (accept_3_5 23 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 240 (accept_3_5 20 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 240 (Polychromatic418967fa.accept_22_19_17_20_1_14411 19 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 240
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 240 (accept_3_5 17 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 240 (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 240 (accept_3_5 14 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 240 (accept_3_5 11 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 240 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 240 (accept_3_5 8 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 127 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 240 (accept_3_5 5 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 127 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 240 (accept_3_5 2 127 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 240 (Polychromatic418967fa.accept_19_1_13_12_1_7748 1 127 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 126 240 (Eq.refl Bool.true) (allA_succ_of_gcd 114 126 240 6 19 21 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 126 240
  (Polychromatic418967fa.accept_22_3_16_20_1_14405 113 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 112 126 240 2 56 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 111 126 240 3 37 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 126 240 2 55 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 126 240
  (Polychromatic418967fa.accept_22_21_16_20_1_11408 109 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 126 240 6 18 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 126 240 (Polychromatic418967fa.accept_13_3_9_6_1_502 107 126 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 126 240 2 53 63 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 126 240 3 35 42 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 126 240 2 52 63 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 126 240
  (Polychromatic418967fa.accept_27_22_18_24_1_14410 103 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 126 240 6 17 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 126 240 (Polychromatic418967fa.accept_13_10_9_6_1_1026 101 126 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 126 240 2 50 63 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 126 240 3 33 42 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 126 240 2 49 63
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 126 240
  (Polychromatic418967fa.accept_17_12_7_2_1_4561 97 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 240 6 16 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 240 (Polychromatic418967fa.accept_11_7_5_9_1_884 95 126 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 126 240 2 47 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 126 240 3 31 42 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 126 240 2 46 63 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 126 240
  (Polychromatic418967fa.accept_22_3_16_20_1_14405 91 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 126 240 6 15 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 126 240 (Polychromatic418967fa.accept_23_20_11_10_1_12913 89 126 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 240 2 44 63 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 126 240 3 29 42 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 126 240 2 43 63
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 126 240
  (Polychromatic418967fa.accept_13_7_9_6_1_148 85 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 240 6 14 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 240 (Polychromatic418967fa.accept_17_15_7_2_1_2303 83 126 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 240 2 41 63 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 126 240 3 27 42 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 126 240 2 40 63 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 126 240
  (Polychromatic418967fa.accept_13_1_9_6_1_146 79 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 240 6 13 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 240 (Polychromatic418967fa.accept_17_9_7_2_1_2347 77 126 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 126 240 2 38 63 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 126 240 3 25 42 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 126 240 2 37 63 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 126 240
  (Polychromatic418967fa.accept_11_7_5_9_1_884 73 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 240 6 12 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 240 (Polychromatic418967fa.accept_22_5_16_20_1_8167 71 126 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 240 2 35 63 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 126 240 3 23 42 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 126 240 2 34 63 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 240
  (Polychromatic418967fa.accept_13_2_9_6_1_501 67 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 240 6 11 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 240 (Polychromatic418967fa.accept_22_21_16_20_1_11408 65 126 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 240 2 32 63 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 126 240 3 21 42 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 126 240 2 31 63 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 240
  (Polychromatic418967fa.accept_25_11_1_15_1_14409 61 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 126 240 6 10 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 126 240 (Polychromatic418967fa.accept_13_7_9_6_1_148 59 126 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 240 2 29 63 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 126 240 3 19 42 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 126 240 2 28 63 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 240
  (Polychromatic418967fa.accept_13_3_9_6_1_502 55 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 240 6 9 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 126 240 (Polychromatic418967fa.accept_13_1_9_6_1_146 53 126 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 240 2 26 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 126 240 3 17 42 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 126 240 2 25 63 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 240
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 49 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 240 6 8 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 126 240 (Polychromatic418967fa.accept_17_13_7_2_1_4562 47 126 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 240 2 23 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 126 240 3 15 42 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 126 240 2 22 63 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 240
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 43 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 240 6 7 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 126 240 (Polychromatic418967fa.accept_13_2_9_6_1_501 41 126 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 240 2 20 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 126 240 3 13 42 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 126 240 2 19 63 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 240
  (Polychromatic418967fa.accept_25_12_1_15_1_14408 37 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 126 240 6 6 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 126 240 (Polychromatic418967fa.accept_25_10_1_15_1_14407 35 126 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 240 2 17 63 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 126 240 3 11 42 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 126 240 2 16 63
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 240
  (Polychromatic418967fa.accept_27_4_18_24_1_14406 31 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 126 240 6 5 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 126 240 (Polychromatic418967fa.accept_11_7_5_9_1_884 29 126 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 240 2 14 63 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 126 240 3 9 42 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 126 240 2 13 63 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 240
  (Polychromatic418967fa.accept_22_3_16_20_1_14405 25 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 126 240 6 4 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 126 240 (Polychromatic418967fa.accept_13_10_9_6_1_1026 23 126 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 240 2 11 63 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 240 3 7 42 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 240 2 10 63 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 240
  (Polychromatic418967fa.accept_25_19_1_15_1_14328 19 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 126 240 6 3 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 126 240 (Polychromatic418967fa.accept_13_4_9_6_1_2376 17 126 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 240 2 8 63 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 126 240 3 5 42 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 240 2 7 63 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 240
  (Polychromatic418967fa.accept_17_13_7_2_1_4562 13 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 240 6 2 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 126 240 (Polychromatic418967fa.accept_22_11_16_20_1_12958 11 126 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 240 2 5 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 126 240 3 3 42 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 126 240 2 4 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 240
  (Polychromatic418967fa.accept_11_7_5_9_1_884 7 126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 240 6 1 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 240 (Polychromatic418967fa.accept_22_5_16_20_1_8167 5 126 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 240 2 2 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 126 240 3 1 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 240 2 1 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 240 (Polychromatic418967fa.accept_13_1_9_6_1_146 1
  126 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 125 240 (Eq.refl Bool.true) (allA_succ_of_gcd 115 125 240 5 23 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 114 125 240
  (Polychromatic418967fa.accept_17_12_6_2_1_2346 114 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 125 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 113 125 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 125 240 (accept_3_4 112 125 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 125 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 111 125
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 125 240 5 22 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 125 240 (accept_3_4
  109 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 125 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 108 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 125 240 (Polychromatic418967fa.accept_21_2_20_9_1_2507 107 125 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 125 240 (accept_3_4 106 125 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 105 125 240 5 21 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 125 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 104 125
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 125 240 (accept_3_4 103 125
  240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 125 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 102 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 125 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 101 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 125 240 5 20 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 125 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 99
  125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 125 240
  (Polychromatic418967fa.accept_17_13_6_2_1_5850 98 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 125 240 (accept_3_4 97 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 125 240 (Polychromatic418967fa.accept_19_1_11_12_1_6112 96 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 95 125 240 5 19 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 94 125 240 (accept_3_4 94 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 125 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 93 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 125 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 92 125 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 125 240 (accept_3_4 91 125 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 125 240 5 18 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 125 240
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 89 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 125 240 (accept_3_4 88 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 125 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 125 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 86 125 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 125 240 5 17 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 125 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 84 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 125 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 83 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 125 240 (accept_3_4 82 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 125 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 125 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 125 240 5 16 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 125 240 (accept_3_4 79 125 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 125 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 125 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 77 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 125 240 (accept_3_4 76 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  125 240 5 15 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 125 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 240 (accept_3_4 73 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 125 240 (Polychromatic418967fa.accept_17_4_6_2_1_5871 72 125 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 125 240 5 14 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 125 240 (Polychromatic418967fa.accept_17_1_6_2_1_623 69 125 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 125 240 (Polychromatic418967fa.accept_9_5_8_6_1_281
  68 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 240 (accept_3_4 67
  125 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 125 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 66 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 125 240 5 13 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 125 240 (accept_3_4 64 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 125 240 (Polychromatic418967fa.accept_13_11_8_6_1_1023 63 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 240 (Polychromatic418967fa.accept_19_5_11_12_1_11765 62
  125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 240 (accept_3_4 61
  125 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 125 240 5 12 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 125 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 240 (accept_3_4 58 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 56 125 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 125 240 5 11 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 125 240
  (Polychromatic418967fa.accept_13_2_8_6_1_2390 54 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 125 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 240 (accept_3_4 52 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 125 240 (Polychromatic418967fa.accept_18_15_17_6_1_4043 51 125 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 125 240 5 10 25 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 125 240 (accept_3_4 49 125 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 48
  125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 240 (accept_3_4 46 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  125 240 5 9 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 125 240 (Polychromatic418967fa.accept_21_2_20_9_1_2507 44 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 125 240 (accept_3_4 43 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 125 240 (Polychromatic418967fa.accept_19_4_11_12_1_13189 42 125 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 240 (Polychromatic418967fa.accept_9_5_8_6_1_281
  41 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 125 240 5 8 25 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 125 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 125 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 240 (accept_3_4 37 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 125 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 125 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 125 240 5 7 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 125 240 (accept_3_4 34 125 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 240 (Polychromatic418967fa.accept_18_15_17_6_1_4043 33 125
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 240 (accept_3_4 31 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  125 240 5 6 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 125 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 125 240 (accept_3_4 28 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 125 240 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 240 (Polychromatic418967fa.accept_19_7_11_12_1_13190 26
  125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 125 240 5 5 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 125 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 125 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 240 (accept_3_4 22 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 125 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 125 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 125 240 5 4 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 125 240 (accept_3_4 19 125 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 125 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 240 (accept_3_4 16 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  125 240 5 3 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 125 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 125 240 (accept_3_4 13 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 125 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 125 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 125 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 125 240 5 2 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 125 240
  (Polychromatic418967fa.accept_22_9_15_20_1_14404 9 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 125 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 240 (accept_3_4 7 125 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 240 (Polychromatic418967fa.accept_21_6_20_9_1_6943 6 125 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 125 240 5 1 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 125 240 (accept_3_4 4 125 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 125 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 240 (accept_3_4 1 125 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 124 240 (Eq.refl Bool.true) (allA_succ_of_gcd 116 124 240 4 29 31 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 124 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 115 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 124 240 2 57 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 124 240 (accept_3_5 113 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 124 240 4 28 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 124 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 111 124 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 124 240 2 55 62 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 124 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 109 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 124 240 4 27 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 124 240 (accept_3_5 107 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 124 240 2 53 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 124 240 (Polychromatic418967fa.accept_11_6_3_9_1_906 105 124 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 124 240 4 26 31 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 124 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 103 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 124 240 2 51 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 124 240 (accept_3_5 101 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 124 240 4 25 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 124 240 (Polychromatic418967fa.accept_17_14_5_2_1_4559 99 124 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 124 240 2 49 62 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 124 240
  (Polychromatic418967fa.accept_19_2_10_12_1_3446 97 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 124 240 4 24 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 124 240 (accept_3_5 95 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 124 240 2 47 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 124 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 93 124 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 124 240 4 23 31 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 124 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 91 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 124 240 2 45 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 124 240 (accept_3_5 89 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 124 240 4 22 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 124 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 124 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 124 240 2 43 62 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 124 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 85 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 124 240 4 21 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 124 240 (accept_3_5 83 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 124 240 2 41 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 124 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 124 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 124 240 4 20 31 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 124 240
  (Polychromatic418967fa.accept_13_1_7_6_1_142 79 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 124 240 2 39 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 124 240 (accept_3_5 77 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 124 240 4 19 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 124 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 75 124 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 124 240 2 37 62 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 124 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 73 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 124 240 4 18 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 240 (accept_3_5 71 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 240 2 35 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 240 (Polychromatic418967fa.accept_13_4_7_6_1_2359 69 124 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 240 4 17 31 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 240 2 33 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 240 (accept_3_5 65 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 240 4 16 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 240 (Polychromatic418967fa.accept_14_7_12_2_1_2502 63 124 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 240 2 31 62 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 240
  (Polychromatic418967fa.accept_11_6_3_9_1_906 61 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 124 240 4 15 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 124 240 (accept_3_5 59 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 240 2 29 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 124 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 240 4 14 31 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 55 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 240 2 27 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 240 (accept_3_5 53 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 240 4 13 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 240 (Polychromatic418967fa.accept_13_12_7_6_1_1015 51 124 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 240 2 25 62 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 240 4 12 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 240 (accept_3_5 47 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 240 2 23 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 124 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 240 4 11 31 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 240
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 43 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 240 2 21 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 240 (accept_3_5 41 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 240 4 10 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 124 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 240 2 19 62 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 240 4 9 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 124 240 (accept_3_5 35 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  124 240 2 17 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 124 240 (Polychromatic418967fa.accept_17_16_5_2_1_9724 33 124 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 240 4 8 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 31
  124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 124 240 2 15 62 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 240 (accept_3_5 29
  124 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 240 4 7 31 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 240
  (Polychromatic418967fa.accept_13_1_7_6_1_142 27 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 124 240 2 13 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 124 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 124 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 240 4 6 31 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 240 (accept_3_5 23 124 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 240 2 11 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 240 4 5 31 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 240 2 9 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 124 240 (accept_3_5 17 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 124 240 4 4 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 124 240 (Polychromatic418967fa.accept_18_15_16_6_1_1751 15 124 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 240 2 7 62 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 240 4 3 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 124 240 (accept_3_5 11 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  124 240 2 5 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 124 240 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 124 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 240 4 2 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 240 (Polychromatic418967fa.accept_14_7_12_2_1_2502 7 124 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 240 2 3 62 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 240 (accept_3_5 5
  124 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 240 4 1 31 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 124 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 124 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 124 240 2 1 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 124 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 124 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 124
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 123 240 (Eq.refl Bool.true) (allA_succ_of_gcd 117 123 240 3 39 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 123 240
  (Polychromatic418967fa.accept_19_2_9_12_1_2237 116 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 123 240 (Polychromatic418967fa.accept_19_1_9_12_1_6207 115 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 123 240 3 38 41 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 123 240
  (Polychromatic418967fa.accept_18_5_15_6_1_3999 113 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 123 240 (Polychromatic418967fa.accept_18_4_15_6_1_3994 112 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 123 240 3 37 41 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 123 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 110 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 123 240 (Polychromatic418967fa.accept_19_14_9_12_1_9113 109 123 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 123 240 3 36 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 123 240
  (Polychromatic418967fa.accept_14_9_11_2_1_2501 107 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 123 240 (Polychromatic418967fa.accept_11_7_2_9_1_480 106 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 123 240 3 35 41 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 123 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 104 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 123 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 103 123 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 123 240 3 34 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 123 240
  (Polychromatic418967fa.accept_18_11_15_6_1_2832 101 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 123 240 (Polychromatic418967fa.accept_17_15_4_2_1_8419 100 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 123 240 3 33 41 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 123 240
  (Polychromatic418967fa.accept_19_3_9_12_1_6253 98 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 123 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 97 123 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 123 240 3 32 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 123 240 (Polychromatic418967fa.accept_11_7_2_9_1_480
  95 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 123 240
  (Polychromatic418967fa.accept_17_9_4_2_1_2298 94 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 123 240 3 31 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 123 240 (Polychromatic418967fa.accept_11_4_2_9_1_496 92 123 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 240 (Polychromatic418967fa.accept_17_6_4_2_1_5889
  91 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 123 240 3 30 41 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 123 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 89 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 240 (Polychromatic418967fa.accept_18_16_15_6_1_4039 88 123 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 123 240 3 29 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 123 240
  (Polychromatic418967fa.accept_19_10_9_12_1_4774 86 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 123 240 (Polychromatic418967fa.accept_21_1_18_9_1_5290 85 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 123 240 3 28 41 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 123 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 123 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 82 123 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 123 240 3 27 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 123 240 (Polychromatic418967fa.accept_17_12_4_2_1_7116
  80 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 240
  (Polychromatic418967fa.accept_14_9_11_2_1_2501 79 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 123 240 3 26 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 123 240 (Polychromatic418967fa.accept_17_9_4_2_1_2298 77 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 123 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 76 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 123 240 3 25 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 123 240 (Polychromatic418967fa.accept_17_6_4_2_1_5889 74 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 240
  (Polychromatic418967fa.accept_11_7_2_9_1_480 73 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 123 240 3 24 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 123 240 (Polychromatic418967fa.accept_18_17_15_6_1_1797 71 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 240
  (Polychromatic418967fa.accept_11_4_2_9_1_496 70 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 123 240 3 23 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 123 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 123 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 240
  (Polychromatic418967fa.accept_19_10_9_12_1_4774 67 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 123 240 3 22 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 123 240 (Polychromatic418967fa.accept_14_9_11_2_1_2501 65 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 240
  (Polychromatic418967fa.accept_18_10_15_6_1_6621 64 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 123 240 3 21 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 123 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 61 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 123 240 3 20 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 123 240 (Polychromatic418967fa.accept_11_4_2_9_1_496 59 123 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 240
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 58 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 123 240 3 19 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 123 240 (Polychromatic418967fa.accept_19_18_9_12_1_6153 56 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 55 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 123 240 3 18 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 123 240 (Polychromatic418967fa.accept_18_17_15_6_1_1797 53 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 240
  (Polychromatic418967fa.accept_18_16_15_6_1_4039 52 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 123 240 3 17 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 123 240 (Polychromatic418967fa.accept_21_8_18_9_1_5329 50 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 240
  (Polychromatic418967fa.accept_17_15_4_2_1_8419 49 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 123 240 3 16 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 123 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 123 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 240
  (Polychromatic418967fa.accept_17_12_4_2_1_7116 46 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 123 240 3 15 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 123 240 (Polychromatic418967fa.accept_23_21_8_10_1_14403 44 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 240
  (Polychromatic418967fa.accept_17_9_4_2_1_2298 43 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 123 240 3 14 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 123 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 123 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 240 (Polychromatic418967fa.accept_7_5_4_2_1_235
  40 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 123 240 3 13 41 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 123 240
  (Polychromatic418967fa.accept_21_17_18_9_1_9968 38 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 123 240 (Polychromatic418967fa.accept_11_4_2_9_1_496 37 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 240 3 12 41 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 240
  (Polychromatic418967fa.accept_18_17_15_6_1_1797 35 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 123 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 123 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 123 240 3 11 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 123 240
  (Polychromatic418967fa.accept_17_15_4_2_1_8419 32 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 123 240 (Polychromatic418967fa.accept_21_10_18_9_1_8500 31 123 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 123 240 3 10 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 123 240
  (Polychromatic418967fa.accept_11_7_2_9_1_480 29 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 240 (Polychromatic418967fa.accept_18_10_15_6_1_6621 28 123 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 240 3 9 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 240 (Polychromatic418967fa.accept_21_4_18_9_1_6899 25 123 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 240 3 8 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 240 (Polychromatic418967fa.accept_14_9_11_2_1_2501
  23 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 240
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 22 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 123 240 3 7 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 123 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 123 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 123 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 240 3 6 41 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 240
  (Polychromatic418967fa.accept_18_17_15_6_1_1797 17 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 123 240 (Polychromatic418967fa.accept_18_16_15_6_1_4039 16 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 240 3 5 41 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 240
  (Polychromatic418967fa.accept_19_14_9_12_1_9113 14 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 123 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 123 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 240 3 4 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 240
  (Polychromatic418967fa.accept_18_11_15_6_1_2832 11 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 123 240 (Polychromatic418967fa.accept_18_10_15_6_1_6621 10 123 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 240 3 3 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 240
  (Polychromatic418967fa.accept_21_8_18_9_1_5329 8 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 240 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 123 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 240 3 2 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 123 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 240
  (Polychromatic418967fa.accept_11_4_2_9_1_496 4 123 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 123 240 3 1 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 123 240 (Polychromatic418967fa.accept_19_2_9_12_1_2237 2 123 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 240 (Polychromatic418967fa.accept_19_1_9_12_1_6207 1 123
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 122 240 (Eq.refl Bool.true) (allA_succ_of_gcd 118 122 240 2 59 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 122 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 117 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 122 240 2 58 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 122 240 (accept_3_4 115 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 122 240 2 57 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 122 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 113 122 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 122 240 2 56 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 122 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 111 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 122 240 2 55 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 122 240 (accept_3_4 109 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 122 240 2 54 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 122 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 107 122 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 122 240 2 53 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 122 240
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 105 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 122 240 2 52 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 122 240 (accept_3_4 103 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 122 240 2 51 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 122 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 101 122 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 122 240 2 50 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 122 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 99 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 122 240 2 49 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 122 240 (accept_3_4 97 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 122 240 2 48 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 122 240 (Polychromatic418967fa.accept_13_4_5_6_1_3201 95 122 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 122 240 2 47 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 122 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 93 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 122 240 2 46 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 122 240 (accept_3_4 91 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 122 240 2 45 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 122 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 122 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 240 2 44 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 240
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 87 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 240 2 43 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 240 (accept_3_4 85 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 240 2 42 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 122 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 240 2 41 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 240
  (Polychromatic418967fa.accept_13_3_5_6_1_3192 81 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 122 240 2 40 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 122 240 (accept_3_4 79 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 240 2 39 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 240 (Polychromatic418967fa.accept_13_12_5_6_1_1050 77 122 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 240 2 38 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 240 2 37 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 240 (accept_3_4 73 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 240 2 36 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 122 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 240 2 35 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 240 2 34 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 240 (accept_3_4 67 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 240 2 33 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 65 122 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 240 2 32 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 240
  (Polychromatic418967fa.accept_13_11_5_6_1_519 63 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 240 2 31 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 240 (accept_3_4 61 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 240 2 30 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 240 (Polychromatic418967fa.accept_31_28_29_23_1_14402 59 122 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 240 2 29 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 240 2 28 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 240 (accept_3_4 55 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 240 2 27 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 122 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 240 2 26 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 240
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 51 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 240 2 25 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 240 (accept_3_4 49 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 240 2 24 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 122 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 240 2 23 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 240
  (Polychromatic418967fa.accept_17_11_3_2_1_5867 45 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 240 2 22 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 240 (accept_3_4 43 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 240 2 21 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 122 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 240 2 20 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 240 2 19 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 240 (accept_3_4 37 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 240 2 18 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 122 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 240 2 17 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 240 2 16 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 240 (accept_3_4 31 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 240 2 15 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 122 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 240 2 14 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 240 2 13 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 240 (accept_3_4 25 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 240 2 12 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 240 (Polychromatic418967fa.accept_13_10_5_6_1_1671 23 122 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 240 2 11 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 240 2 10 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 240 (accept_3_4 19 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 240 2 9 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 122 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 240 2 8 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 240 2 7 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 240 (accept_3_4 13 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 240 2 6 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 122 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 240 2 5 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 240
  (Polychromatic418967fa.accept_18_9_14_6_1_1790 9 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 240 2 4 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 240 (accept_3_4 7 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  240 2 3 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 122 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 240 2 2 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 122 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 240 2 1 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 240 (accept_3_4 1 122 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 121 240 (Eq.refl Bool.true) (allA_succ_of_accept 119 121 240 (accept_3_5 119 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 118 121 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 240
  (Polychromatic418967fa.accept_18_9_13_6_1_877 117 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 121 240 (accept_3_5 116 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 115 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 121 240 (Polychromatic418967fa.accept_13_10_4_6_1_3224 114 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 240 (accept_3_5 113 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 240 (Polychromatic418967fa.accept_21_7_16_9_1_2417 112
  121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 121 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 111 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 121 240 (accept_3_5 110 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 109 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 121 240 (Polychromatic418967fa.accept_21_3_16_9_1_8528 108 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 121 240 (accept_3_5 107 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 106 121
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 240
  (Polychromatic418967fa.accept_14_7_9_2_1_2489 105 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 121 240 (accept_3_5 104 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 121 240 (Polychromatic418967fa.accept_19_8_7_12_1_14355 103 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 121 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 102 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 240 (accept_3_5 101 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 100 121 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 240
  (Polychromatic418967fa.accept_18_9_13_6_1_877 99 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 240 (accept_3_5 98 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 97 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 240 (Polychromatic418967fa.accept_13_5_4_6_1_2371 96 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 240 (accept_3_5 95 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 240 (Polychromatic418967fa.accept_19_18_7_12_1_6148 94 121
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 93 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 240 (accept_3_5 92 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 91 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 240 (Polychromatic418967fa.accept_19_14_7_12_1_7732 90 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 240 (accept_3_5 89 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 88 121 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 240
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 87 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 240 (accept_3_5 86 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 240 (Polychromatic418967fa.accept_13_7_4_6_1_3221 85 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 84 121 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 240 (accept_3_5 83 121 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 82 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 240
  (Polychromatic418967fa.accept_14_11_9_2_1_6382 81 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 240 (accept_3_5 80 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 79 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 240 (Polychromatic418967fa.accept_21_15_16_9_1_5303 78 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 240 (accept_3_5 77 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 240 (Polychromatic418967fa.accept_13_11_4_6_1_1006 76 121
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 75 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 240 (accept_3_5 74 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 73 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 240 (Polychromatic418967fa.accept_13_7_4_6_1_3221 72 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 240 (accept_3_5 71 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 121 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 240
  (Polychromatic418967fa.accept_21_6_16_9_1_5300 69 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 240 (accept_3_5 68 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 240 (Polychromatic418967fa.accept_13_2_4_6_1_2356 67 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 121 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 240 (accept_3_5 65 121 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 240
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 63 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 121 240 (accept_3_5 62 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 121 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 60 121 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 240 (accept_3_5 59 121 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 240 (Polychromatic418967fa.accept_19_1_7_12_1_3443 58 121 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 240 (accept_3_5 56 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 240 (Polychromatic418967fa.accept_13_2_4_6_1_2356 54 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 240 (accept_3_5 53 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 121 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 240
  (Polychromatic418967fa.accept_28_23_9_16_1_14401 51 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 121 240 (accept_3_5 50 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 121 240 (Polychromatic418967fa.accept_13_10_4_6_1_3224 49 121 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 121 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 240 (accept_3_5 47 121 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 46
  121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 240
  (Polychromatic418967fa.accept_18_9_13_6_1_877 45 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 240 (accept_3_5 44 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 240 (Polychromatic418967fa.accept_19_4_7_12_1_6201 42 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 240 (accept_3_5 41 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 240 (Polychromatic418967fa.accept_23_17_6_10_1_14400 40
  121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 240 (accept_3_5 38 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 240 (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 240 (accept_3_5 35 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 121 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 240
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 33 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 240 (accept_3_5 32 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 240 (Polychromatic418967fa.accept_13_5_4_6_1_2371 31 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 121 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 240 (accept_3_5 29 121 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 240
  (Polychromatic418967fa.accept_18_9_13_6_1_877 27 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 240 (accept_3_5 26 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 240 (Polychromatic418967fa.accept_13_11_4_6_1_1006 24 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 240 (accept_3_5 23 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 240 (Polychromatic418967fa.accept_13_9_4_6_1_1005 22 121
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 240 (accept_3_5 20 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 240 (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 240 (accept_3_5 17 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 121 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 240
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 15 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 240 (accept_3_5 14 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 240 (Polychromatic418967fa.accept_21_13_16_9_1_2541 13 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 121 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 240 (accept_3_5 11 121 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 240
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 240 (accept_3_5 8 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 240 (Polychromatic418967fa.accept_21_6_16_9_1_5300 6 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 240 (accept_3_5 5 121 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 4 121 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 240 (accept_3_5 2 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 121 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 240 (allA_succ_of_accept 119 120 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 119 120 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 120 240 2 59 60 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 117 120 240 3 39 40 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 120 240 4 29 30 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 115 120 240 5 23 24
  48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 114 120 240 6 19
  20 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 120 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 113 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 120 240 8 14 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 120 240 3 37 40 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 120 240 10 11 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 109 120 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 120 240 12 9 10 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 120 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 107 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 120 240 2 53 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 120 240 15 7 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 120 240 8 13 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 103 120
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 120 240 6 17 20 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 120 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 101 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 120 240 20 5 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 120 240 3 33 40 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 120 240 2 49 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 120 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 97 120 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 120 240 24 4 5 10 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 120 240 5 19 24 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 120 240 2 47 60
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 120 240 3 31
  40 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 120 240 4
  23 30 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120
  240 (Polychromatic418967fa.accept_9_1_3_6_1_70 91 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 240 30 3 4 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 120 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 89 120 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 120 240 8 11 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 120 240 3 29 40 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 120 240 2 43 60 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 120 240 5 17 24 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 120 240 12 7 10 20
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 120 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 83 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 120 240 2 41 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 120 240 3 27 40 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 120 240 40 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 120 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 120 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 120 240 6 13 20 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 120 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 77 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 120 240 4 19 30 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 120 240 15 5 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 120 240 2 37 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 120 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 73 120 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 120 240 24 3 5 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 120 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 71 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 120 240 10 7 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 120 240 3 23 40 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 120 240 4 17 30 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 67 120 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 120 240 6 11 20 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 120 240 5 13 24 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 120 240 8 8 15 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 120 240 3 21 40
  80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 120 240 2 31
  60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 61 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 240 60 1 2 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 120 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 120 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 240 2 29 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 120 240 3 19 40 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 120 240 8 7 15 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 120 240 5 11 24 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 120 240 6 9 20 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 120 240 4 13 30 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 120 240 3 17 40 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 120 240 10 5 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 120 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 240 24 2 5 10 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 120 240 2 23 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 120 240 15 3 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 120 240 4 11 30 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 120 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 120 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 240 6 7 20 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 240 40 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 120 240 3 13 40 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 120 240 2 19 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 120 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 120 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 240 12 3 10 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 120 240 5 7 24 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 120 240 2 17 60 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 120 240 3 11 40 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 240 8 4 15 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 240 30 1 4 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 120 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 240 4 7 30 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 120 240 3 9 40 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 120 240 2 13 60 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 120 240 5 5 24 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 240 24 1 5 10 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 240 2 11 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 120 240 3 7 40 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 120 240 20 1 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 120 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 120 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 240 6 3 20 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 240 8 2 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 120 240 15 1 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 120 240 2 7 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 120 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 120 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 240 12 1 10 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 240 10 1 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 120 240 3 3 40 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 120 240 8 1 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 120 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 120 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 240 6 1 20 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 120 240 5 1 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 120 240 4 1 30 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 120 240 3 1 40 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 120 240 2 1 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 1
  120 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 240 (allA_succ_of_accept 118 119 240 (accept_3_4 118 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 240 (Polychromatic418967fa.accept_14_5_7_2_1_468 117 119 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 116 119
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 240 (accept_3_4 115 119
  240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 240
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 114 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 119 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 113 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 240 (accept_3_4 112 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 111 119
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 240
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 110 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 119 240 (accept_3_4 109 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 119 240 (Polychromatic418967fa.accept_13_4_2_6_1_1043 108 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 240 (Polychromatic418967fa.accept_9_8_2_6_1_875
  107 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 240 (accept_3_4
  106 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 240
  (Polychromatic418967fa.accept_13_1_2_6_1_515 105 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 119 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 104 119 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 119 240 (accept_3_4 103 119 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 102 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 119 240
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 101 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 119 240 (accept_3_4 100 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 119 240 (Polychromatic418967fa.accept_13_8_2_6_1_2385 99 119 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 98 119 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 119 240 (accept_3_4 97 119 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 119 240
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 96 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 119 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 95 119 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 240 (accept_3_4 94 119 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 93 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 240 (Polychromatic418967fa.accept_13_1_2_6_1_515
  92 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 119 240 (accept_3_4 91
  119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 119 240
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 90 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 119 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 89 119 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 240 (accept_3_4 88 119 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 119 240 (Polychromatic418967fa.accept_13_9_2_6_1_514 87 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 86 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 240 (accept_3_4 85 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 119 240 (Polychromatic418967fa.accept_19_7_5_12_1_7756 83 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 240 (accept_3_4 82 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 240 (Polychromatic418967fa.accept_21_18_14_9_1_5351 81 119
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 80 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 119 240 (accept_3_4 79 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 119 240 (Polychromatic418967fa.accept_21_15_14_9_1_2540 78 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 119 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 77 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 240 (accept_3_4 76 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 240
  (Polychromatic418967fa.accept_13_9_2_6_1_514 74 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 119 240 (accept_3_4 73 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 119 240 (Polychromatic418967fa.accept_19_15_5_12_1_13123 72 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 71 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 240 (accept_3_4 70 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 240 (Polychromatic418967fa.accept_13_4_2_6_1_1043 69 119
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 68 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 240 (accept_3_4 67 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 240 (Polychromatic418967fa.accept_14_9_7_2_1_2483 65 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 240 (accept_3_4 64 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 240 (Polychromatic418967fa.accept_23_17_4_10_1_9674 63 119
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 240 (accept_3_4 61 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 240 (Polychromatic418967fa.accept_13_8_2_6_1_2385 60 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 240 (accept_3_4 58 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 240
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 56 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 240 (accept_3_4 55 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 240 (Polychromatic418967fa.accept_14_12_7_2_1_1663 54 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 240 (accept_3_4 52 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 240 (Polychromatic418967fa.accept_13_12_2_6_1_2396 51 119 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 240 (accept_3_4 49 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 240 (Polychromatic418967fa.accept_13_8_2_6_1_2385 47 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 240 (accept_3_4 46 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 240 (Polychromatic418967fa.accept_19_7_5_12_1_7756 45 119
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 240 (accept_3_4 43 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 240 (Polychromatic418967fa.accept_19_4_5_12_1_3441 42 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 240 (accept_3_4 40 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 240
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 38 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 240 (accept_3_4 37 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 240 (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 240 (accept_3_4 34 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 240 (Polychromatic418967fa.accept_14_5_7_2_1_468 33 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 240 (accept_3_4 31 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 240 (Polychromatic418967fa.accept_22_7_9_20_1_14366 29 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 240 (accept_3_4 28 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 240 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 119
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 240 (accept_3_4 25 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 240 (Polychromatic418967fa.accept_21_3_14_9_1_5299 24 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 240 (accept_3_4 22 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 240
  (Polychromatic418967fa.accept_19_1_5_12_1_6249 20 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 240 (accept_3_4 19 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 240 (Polychromatic418967fa.accept_21_18_14_9_1_5351 18 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 240 (accept_3_4 16 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 240 (Polychromatic418967fa.accept_18_15_11_6_1_4067 15 119 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 240 (accept_3_4 13 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 240 (Polychromatic418967fa.accept_19_11_5_12_1_3439 11 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 240 (accept_3_4 10 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 240 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 119 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 240 (accept_3_4 7 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 240 (Polychromatic418967fa.accept_21_6_14_9_1_6854 6 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 240 (accept_3_4 4 119 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 119 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 240
  (Polychromatic418967fa.accept_21_2_14_9_1_3866 2 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 240 (accept_3_4 1 119 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 240 (allA_succ_of_accept 117 118 240 (Polychromatic418967fa.accept_21_12_13_9_1_2482 117 118 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 118 240 2 58 59 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 118 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 115 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 118 240 2 57 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 118 240 (accept_3_5 113 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 118 240 2 56 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 118 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 111 118 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 118 240 2 55 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 118 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 109 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 118 240 2 54 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 118 240 (accept_3_5 107 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 118 240 2 53 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 118 240 (Polychromatic418967fa.accept_18_15_10_6_1_1781 105 118 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 118 240 2 52 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 118 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 103 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 118 240 2 51 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 118 240 (accept_3_5 101 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 118 240 2 50 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 118 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 99 118 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 118 240 2 49 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 118 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 97 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 118 240 2 48 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 118 240 (accept_3_5 95 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 118 240 2 47 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 118 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 93 118 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 118 240 2 46 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 118 240
  (Polychromatic418967fa.accept_21_7_13_9_1_6937 91 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 118 240 2 45 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 118 240 (accept_3_5 89 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 118 240 2 44 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 118 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 118 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 118 240 2 43 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 118 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 85 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 118 240 2 42 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 118 240 (accept_3_5 83 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 118 240 2 41 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 118 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 118 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 118 240 2 40 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 118 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 79 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 118 240 2 39 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 118 240 (accept_3_5 77 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 118 240 2 38 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 118 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 75 118 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 118 240 2 37 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 118 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 73 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 118 240 2 36 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 118 240 (accept_3_5 71 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 118 240 2 35 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 118 240 (Polychromatic418967fa.accept_17_1_16_2_1_1404 69 118 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 118 240 2 34 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 118 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 67 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 118 240 2 33 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 118 240 (accept_3_5 65 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 118 240 2 32 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 118 240 (Polychromatic418967fa.accept_19_6_4_12_1_6193 63 118 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 240 2 31 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 61 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 118 240 2 30 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 118 240 (accept_3_5 59 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 240 2 29 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 118 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 240 2 28 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 240
  (Polychromatic418967fa.accept_13_3_1_6_1_509 55 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 118 240 2 27 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 118 240 (accept_3_5 53 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 240 2 26 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 240 (Polychromatic418967fa.accept_18_15_10_6_1_1781 51 118 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 240 2 25 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 240 2 24 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 240 (accept_3_5 47 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 240 2 23 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 118 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 240 2 22 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 240 2 21 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 240 (accept_3_5 41 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 240 2 20 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 118 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 240 2 19 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 240
  (Polychromatic418967fa.accept_21_16_13_9_1_2539 37 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 118 240 2 18 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 118 240 (accept_3_5 35 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 240 2 17 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 240 (Polychromatic418967fa.accept_13_7_1_6_1_3287 33 118 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 240 2 16 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 240 2 15 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 240 (accept_3_5 29 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 240 2 14 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 240 (Polychromatic418967fa.accept_19_8_4_12_1_4768 27 118 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 240 2 13 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 240 2 12 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 240 (accept_3_5 23 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 240 2 11 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 118 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 240 2 10 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 240
  (Polychromatic418967fa.accept_22_19_8_20_1_2041 19 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 118 240 2 9 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 118 240 (accept_3_5 17 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 118 240 2 8 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 118 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 118 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 118 240 2 7 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 118 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 118 240 2 6 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 118 240 (accept_3_5 11 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 118 240 2 5 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 118 240 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 118 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 118 240 2 4 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 240 2 3 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 240 (accept_3_5 5 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  240 2 2 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 118 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 240 2 1 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 118 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 118 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 240 (allA_succ_of_accept 116 117 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 116 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 115 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 117 240 3 38 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 117 240 (Polychromatic418967fa.accept_21_8_12_9_1_9980 113 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 240
  (Polychromatic418967fa.accept_11_2_7_9_1_890 112 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 117 240 3 37 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 117 240 (Polychromatic418967fa.accept_18_2_9_6_1_4025 110 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 109 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 117 240 3 36 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 117 240 (Polychromatic418967fa.accept_21_2_12_9_1_5324 107 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 117 240
  (Polychromatic418967fa.accept_17_4_15_2_1_4551 106 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 117 240 3 35 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 117 240 (Polychromatic418967fa.accept_11_5_7_9_1_2696 104 117 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 240
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 103 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 117 240 3 34 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 117 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 101 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 240
  (Polychromatic418967fa.accept_21_16_12_9_1_2475 100 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 117 240 3 33 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 117 240 (Polychromatic418967fa.accept_17_13_15_2_1_654 98 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 240
  (Polychromatic418967fa.accept_18_7_9_6_1_4023 97 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 117 240 3 32 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 117 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 117 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 94
  117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 117 240 3 31 39 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 117 240
  (Polychromatic418967fa.accept_17_7_15_2_1_10843 92 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 117 240 (Polychromatic418967fa.accept_14_7_5_2_1_2473 91 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 117 240 3 30 39 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 117 240
  (Polychromatic418967fa.accept_17_4_15_2_1_4551 89 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 88 117 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 117 240 3 29 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 117 240 (Polychromatic418967fa.accept_18_14_9_6_1_1777
  86 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 240
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 85 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 117 240 3 28 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 117 240 (Polychromatic418967fa.accept_19_7_3_12_1_4787 83 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 240
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 82 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 117 240 3 27 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 117 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 117 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 240 (Polychromatic418967fa.accept_11_2_7_9_1_890
  79 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 117 240 3 26 39 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 117 240
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 77 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 240 (Polychromatic418967fa.accept_21_13_12_9_1_5323 76 117 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 117 240 3 25 39 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 117 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 74 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 117 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 73 117 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 117 240 3 24 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 117 240 (Polychromatic418967fa.accept_11_5_7_9_1_2696
  71 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 240
  (Polychromatic418967fa.accept_19_13_3_12_1_6186 70 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 117 240 3 23 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 117 240 (Polychromatic418967fa.accept_11_2_7_9_1_890 68 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 117 240 3 22 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 117 240 (Polychromatic418967fa.accept_21_2_12_9_1_5324 65 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 240
  (Polychromatic418967fa.accept_17_13_15_2_1_654 64 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 117 240 3 21 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 117 240 (Polychromatic418967fa.accept_18_8_9_6_1_3989 62 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 240
  (Polychromatic418967fa.accept_17_10_15_2_1_653 61 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 117 240 3 20 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 117 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 117 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 240
  (Polychromatic418967fa.accept_17_7_15_2_1_10843 58 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 57 117 240 3 19 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 117 240 (Polychromatic418967fa.accept_18_2_9_6_1_4025 56 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 240
  (Polychromatic418967fa.accept_17_4_15_2_1_4551 55 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 117 240 3 18 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 117 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 117 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 52
  117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 117 240 3 17 39 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 117 240
  (Polychromatic418967fa.accept_18_14_9_6_1_1777 50 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 240 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 117 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 117 240 3 16 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 117 240 (Polychromatic418967fa.accept_17_13_15_2_1_654
  47 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 46 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 117 240 3 15 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 117 240 (Polychromatic418967fa.accept_17_10_15_2_1_653 44 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 240
  (Polychromatic418967fa.accept_18_7_9_6_1_4023 43 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 117 240 3 14 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 117 240 (Polychromatic418967fa.accept_17_7_15_2_1_10843 41 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 240
  (Polychromatic418967fa.accept_19_2_3_12_1_10559 40 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 117 240 3 13 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 117 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 240
  (Polychromatic418967fa.accept_18_1_9_6_1_6630 37 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 240 3 12 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 117 240 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 117 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 240
  (Polychromatic418967fa.accept_19_15_3_12_1_11789 34 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 117 240 3 11 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 117 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 117 240 3 10 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 117 240 (Polychromatic418967fa.accept_19_10_3_12_1_10566 29 117 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 240
  (Polychromatic418967fa.accept_19_9_3_12_1_6191 28 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 117 240 3 9 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 117 240 (Polychromatic418967fa.accept_18_8_9_6_1_3989 26 117 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 117 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 240 3 8 39 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 240
  (Polychromatic418967fa.accept_21_2_12_9_1_5324 23 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 240 (Polychromatic418967fa.accept_21_1_12_9_1_8469 22 117 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 240 3 7 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 240 (Polychromatic418967fa.accept_18_2_9_6_1_4025
  20 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 240
  (Polychromatic418967fa.accept_18_1_9_6_1_6630 19 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 117 240 3 6 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 117 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 117 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 240 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 117
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 240 3 5 39 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 240
  (Polychromatic418967fa.accept_18_14_9_6_1_1777 14 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 240 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 117 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 240 3 4 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 11
  117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 10 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 117 240 3 3 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 117 240 (Polychromatic418967fa.accept_18_8_9_6_1_3989 8 117 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 240 (Polychromatic418967fa.accept_14_7_5_2_1_2473 7 117 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 240 3 2 39 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 240
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 117 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 240 3 1 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 240 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 117 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 240
  (Polychromatic418967fa.accept_18_1_9_6_1_6630 1 117 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 117
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 240 (allA_succ_of_accept 115 116 240 (accept_3_4 115 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 116 240 2 57 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 116 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 113 116 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 116 240 4 28 29 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 116 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 111 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 116 240 2 55 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 116 240 (accept_3_4 109 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 116 240 4 27 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 116 240 (Polychromatic418967fa.accept_14_9_4_2_1_983 107 116 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 116 240 2 53 58 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 116 240
  (Polychromatic418967fa.accept_17_3_14_2_1_646 105 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 116 240 4 26 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 116 240 (accept_3_4 103 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 116 240 2 51 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 116 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 101 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 116 240 4 25 29 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 116 240
  (Polychromatic418967fa.accept_18_9_8_6_1_4021 99 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 116 240 2 49 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 116 240 (accept_3_4 97 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 116 240 4 24 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 116 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 95 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 116 240 2 47 58 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 93 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 116 240 4 23 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 116 240 (accept_3_4 91 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 116 240 2 45 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 116 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 116 240 4 22 29 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 116 240
  (Polychromatic418967fa.accept_25_12_16_15_1_12667 87 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 116 240 2 43 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 116 240 (accept_3_4 85 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 116 240 4 21 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 116 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 240 2 41 58 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 240
  (Polychromatic418967fa.accept_18_9_8_6_1_4021 81 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 116 240 4 20 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 240 (accept_3_4 79 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 240 2 39 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 77 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 240 4 19 29 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 240 2 37 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 240 (accept_3_4 73 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 240 4 18 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 240 (Polychromatic418967fa.accept_17_3_14_2_1_646 71 116 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 240 2 35 58 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 240 4 17 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 240 (accept_3_4 67 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 240 2 33 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 65 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 240 4 16 29 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 240
  (Polychromatic418967fa.accept_18_9_8_6_1_4021 63 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 116 240 2 31 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 116 240 (accept_3_4 61 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 240 4 15 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 240 2 29 58 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 57 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 240 4 14 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 240 (accept_3_4 55 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 240 2 27 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 240 (Polychromatic418967fa.accept_22_9_6_20_1_8174 53 116 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 240 4 13 29 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 240
  (Polychromatic418967fa.accept_14_9_4_2_1_983 51 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 240 2 25 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 240 (accept_3_4 49 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 240 4 12 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 240 2 23 58 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 240
  (Polychromatic418967fa.accept_18_9_8_6_1_4021 45 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 240 4 11 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 240 (accept_3_4 43 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 240 2 21 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 240 4 10 29 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 39 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 240 2 19 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 240 (accept_3_4 37 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 240 4 9 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 240 (Polychromatic418967fa.accept_22_13_6_20_1_14348 35 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 240 2 17 58 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 240 4 8 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 116 240 (accept_3_4 31 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  116 240 2 15 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 116 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 116 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 240 4 7 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 27
  116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 240 2 13 58 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 240 (accept_3_4 25
  116 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 240 4 6 29 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 116 240 2 11 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 116 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 116 240 4 5 29 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 116 240 (accept_3_4 19 116 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 116 240 2 9 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 116 240
  (Polychromatic418967fa.accept_19_17_2_12_1_4751 17 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 116 240 4 4 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 116 240 (Polychromatic418967fa.accept_13_2_12_6_1_2394 15 116 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 240 2 7 58 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 240 (accept_3_4 13 116 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 240 4 3 29 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 240 2 5 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 116 240 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 240 4 2 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 240 (accept_3_4 7 116 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 240 2 3 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 116 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 240 4 1 29 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 240 2 1 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 240 (accept_3_4 1 116 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 240 (allA_succ_of_accept 114 115 240 (Polychromatic418967fa.accept_27_6_7_24_1_14399 114 115 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 240 (accept_3_5 113 115 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 115 240 (Polychromatic418967fa.accept_9_4_7_6_1_255
  112 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 111 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 115 240 5 22 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 115 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 109 115 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 115 240
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 108 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 115 240 (accept_3_5 107 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 115 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 106 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 115 240 5 21 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 115 240 (accept_3_5 104 115 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 115 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 103 115 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 102 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 115 240 (accept_3_5 101 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  100 115 240 5 20 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 99 115 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 99 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 115 240 (accept_3_5 98 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 115 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 97 115 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 115 240 (Polychromatic418967fa.accept_7_5_3_2_1_249
  96 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 115 240 5 19 23 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 115 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 94 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 115 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 93 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 115 240 (accept_3_5 92 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 115 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 91 115 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 115 240 5 18 23 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 115 240 (accept_3_5 89 115 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 240 (Polychromatic418967fa.accept_28_4_3_16_1_14398 88 115
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 240
  (Polychromatic418967fa.accept_19_11_1_12_1_6237 87 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 115 240 (accept_3_5 86 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 115 240 5 17 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 84 115 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 84 115 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 240 (accept_3_5 83 115 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 82 115 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 240
  (Polychromatic418967fa.accept_18_9_7_6_1_5331 81 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 115 240 5 16 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 115 240 (Polychromatic418967fa.accept_21_16_10_9_1_9965 79 115 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 115 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 78 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 115 240 (accept_3_5 77 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 115 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 76 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 115 240 5 15 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 115 240 (accept_3_5 74 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 115 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 240 (Polychromatic418967fa.accept_27_18_7_24_1_12577 72
  115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 240 (accept_3_5 71
  115 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 115 240 5 14 23 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 115 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 240 (accept_3_5 68 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 66 115 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 115 240 5 13 23 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 115 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 64 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 115 240 (Polychromatic418967fa.accept_18_9_7_6_1_5331 63 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 240 (accept_3_5 62 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 115 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 115 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 115 240 5 12 23 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 115 240 (accept_3_5 59 115 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 115 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 240 (accept_3_5 56 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  115 240 5 11 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 115 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 240 (accept_3_5 53 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 115 240 (Polychromatic418967fa.accept_17_1_13_2_1_7086 52 115 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 240
  (Polychromatic418967fa.accept_11_7_5_9_1_884 51 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 115 240 5 10 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 115 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 115 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 240 (Polychromatic418967fa.accept_7_6_3_2_1_461
  48 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 240 (accept_3_5 47
  115 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 46 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 115 240 5 9 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 115 240 (accept_3_5 44 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 240 (Polychromatic418967fa.accept_19_4_1_12_1_4803 42 115 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 240 (accept_3_5 41 115 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 115 240 5 8 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 115 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 39
  115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 240 (accept_3_5 38
  115 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 115 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 115 240 5 7 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 115 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 34
  115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 240 (accept_3_5 32 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 115 240 5 6 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 115 240 (accept_3_5 29 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 115 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 115 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 240 (accept_3_5 26 115 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 115 240 5 5 23 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 115 240
  (Polychromatic418967fa.accept_17_7_13_2_1_10840 24 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 115 240 (accept_3_5 23 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 115 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 115 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 115 240 5 4 23 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 115 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 240 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 240 (accept_3_5 17 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 115 240 (Polychromatic418967fa.accept_21_16_10_9_1_9965 16 115 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 115 240 5 3 23 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 115 240 (accept_3_5 14 115 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 240 (Polychromatic418967fa.accept_7_6_3_2_1_461
  13 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 240 (accept_3_5 11 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  115 240 5 2 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 115 240 (Polychromatic418967fa.accept_18_9_7_6_1_5331 9 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 115 240 (accept_3_5 8 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 115 240 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 115 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 115 240 5 1 23 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 115 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 4 115 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 115 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 240 (accept_3_5 2 115 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 115 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 115 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 240 (allA_succ_of_accept 113 114 240 (Polychromatic418967fa.accept_13_9_10_6_1_1028 113 114 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 114 240 2 56 57 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 111 114 240 3 37 38 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 114 240 2 55 57
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 240
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 109 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 114 240 6 18 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 114 240 (Polychromatic418967fa.accept_13_3_10_6_1_2382 107 114 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 114 240 2 53 57 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 114 240 3 35 38 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 114 240 2 52 57
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 240
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 103 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 114 240 6 17 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 114 240 (Polychromatic418967fa.accept_11_2_4_9_1_484 101 114 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 114 240 2 50 57 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 114 240 3 33 38 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 114 240 2 49 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 240
  (Polychromatic418967fa.accept_22_9_4_20_1_8172 97 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 114 240 6 16 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 114 240 (Polychromatic418967fa.accept_13_4_10_6_1_989 95 114 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 240 2 47 57 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 114 240 3 31 38 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 114 240 2 46 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 114 240
  (Polychromatic418967fa.accept_17_6_12_2_1_10966 91 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 114 240 6 15 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 114 240 (Polychromatic418967fa.accept_17_4_12_2_1_2349 89 114 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 240 2 44 57 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 114 240 3 29 38 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 114 240 2 43 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 114 240
  (Polychromatic418967fa.accept_23_16_22_10_1_14397 85 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 114 240 6 14 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 114 240 (Polychromatic418967fa.accept_13_5_10_6_1_2361 83 114 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 240 2 41 57 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 114 240 3 27 38 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 114 240 2 40 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 114 240
  (Polychromatic418967fa.accept_11_2_4_9_1_484 79 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 240 6 13 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 240 (Polychromatic418967fa.accept_13_12_10_6_1_3212 77 114 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 240 2 38 57 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 114 240 3 25 38 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 114 240 2 37 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 240
  (Polychromatic418967fa.accept_25_23_14_15_1_14396 73 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 114 240 6 12 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 114 240 (Polychromatic418967fa.accept_25_21_14_15_1_14395 71 114 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 240 2 35 57 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 114 240 3 23 38 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 114 240 2 34 57
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 240
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 67 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 240 6 11 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 240 (Polychromatic418967fa.accept_22_21_4_20_1_12954 65 114 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 240 2 32 57 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 114 240 3 21 38 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 114 240 2 31 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 240
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 61 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 240 6 10 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 240 (Polychromatic418967fa.accept_22_15_4_20_1_9799 59 114 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 240 2 29 57 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 114 240 3 19 38 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 114 240 2 28 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 240
  (Polychromatic418967fa.accept_13_3_10_6_1_2382 55 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 240 6 9 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 114 240 (Polychromatic418967fa.accept_22_9_4_20_1_8172 53 114 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 240 2 26 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 114 240 3 17 38 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 114 240 2 25 57 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 240
  (Polychromatic418967fa.accept_25_24_14_15_1_14394 49 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 114 240 6 8 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 114 240 (Polychromatic418967fa.accept_26_21_10_6_1_14393 47 114 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 240 2 23 57 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 114 240 3 15 38 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 114 240 2 22 57
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 240
  (Polychromatic418967fa.accept_13_4_10_6_1_989 43 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 240 6 7 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 114 240 (Polychromatic418967fa.accept_13_2_10_6_1_1676 41 114 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 240 2 20 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 114 240 3 13 38 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 240 2 19 57 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 240
  (Polychromatic418967fa.accept_22_15_4_20_1_9799 37 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 114 240 6 6 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 114 240 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 114 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 240 2 17 57 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 114 240 3 11 38 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 240 2 16 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 240
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 31 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 240 6 5 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 114 240 (Polychromatic418967fa.accept_13_3_10_6_1_2382 29 114 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 240 2 14 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 114 240 3 9 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 240 2 13 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 240
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 25 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 114 240 6 4 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 114 240 (Polychromatic418967fa.accept_17_6_12_2_1_10966 23 114 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 240 2 11 57 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 114 240 3 7 38 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 114 240 2 10 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 240
  (Polychromatic418967fa.accept_28_19_2_16_1_14392 19 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 114 240 6 3 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 114 240 (Polychromatic418967fa.accept_13_4_10_6_1_989 17 114 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 240 2 8 57 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 240 3 5 38 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 240 2 7 57 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 240
  (Polychromatic418967fa.accept_11_2_4_9_1_484 13 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 240 6 2 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 114 240 (Polychromatic418967fa.accept_23_11_22_10_1_12890 11 114 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 240 2 5 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 240 3 3 38 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 240 2 4 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 240
  (Polychromatic418967fa.accept_17_7_12_2_1_7105 7 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 240 6 1 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 240 (Polychromatic418967fa.accept_13_5_10_6_1_2361 5 114 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 240 2 2 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 114 240 3 1 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 114 240 2 1 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 240
  (Polychromatic418967fa.accept_25_1_14_15_1_14391 1 114 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 114
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 240 (allA_succ_of_accept 112 113 240 (accept_3_4 112 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 111 113 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 110 113
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 240 (accept_3_4 109 113
  240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 108 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 107 113 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 240 (accept_3_4 106 113 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 240 (Polychromatic418967fa.accept_11_6_3_9_1_906 105 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 104 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 240 (accept_3_4 103 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 102 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 101 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 240 (accept_3_4 100 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 240 (Polychromatic418967fa.accept_22_11_3_20_1_4879 99 113
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 98 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 240 (accept_3_4 97 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 240 (Polychromatic418967fa.accept_19_1_18_12_1_7755 96 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 240 (Polychromatic418967fa.accept_13_4_9_6_1_2376 95 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 240 (accept_3_4 94 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 93 113 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 92 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 240 (accept_3_4 91 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 89 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 240 (accept_3_4 88 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 240
  (Polychromatic418967fa.accept_25_11_13_15_1_14390 86 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 113 240 (accept_3_4 85 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 113 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 113 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 113 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 113 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 240 (accept_3_4 82 113 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 240 (Polychromatic418967fa.accept_13_3_9_6_1_502
  81 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 240 (accept_3_4 79 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 240 (Polychromatic418967fa.accept_14_8_1_2_1_965 78 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 240 (Polychromatic418967fa.accept_17_9_11_2_1_5894 77 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 240 (accept_3_4 76 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 113 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 74 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 240 (accept_3_4 73 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 240 (Polychromatic418967fa.accept_11_6_3_9_1_906 72 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 71 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 240 (accept_3_4 70 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 240
  (Polychromatic418967fa.accept_13_3_9_6_1_502 68 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 240 (accept_3_4 67 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 65 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 240 (accept_3_4 64 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 240 (Polychromatic418967fa.accept_19_6_18_12_1_6125 63 113 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 240 (accept_3_4 61 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 240 (Polychromatic418967fa.accept_17_9_11_2_1_5894 60 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 240 (accept_3_4 58 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 240 (accept_3_4 55 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 240 (Polychromatic418967fa.accept_13_2_9_6_1_501 54 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 240 (accept_3_4 52 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 240 (Polychromatic418967fa.accept_18_15_5_6_1_5293 51 113 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 240
  (Polychromatic418967fa.accept_11_6_3_9_1_906 50 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 240 (accept_3_4 49 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 240 (accept_3_4 46 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 240 (accept_3_4 43 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 240 (Polychromatic418967fa.accept_13_3_9_6_1_502 42 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 240 (accept_3_4 40 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 240 (accept_3_4 37 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 240 (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 240 (accept_3_4 34 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 240 (Polychromatic418967fa.accept_13_7_9_6_1_148 33 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 240
  (Polychromatic418967fa.accept_19_13_18_12_1_3428 32 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 113 240 (accept_3_4 31 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 113 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 113 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 113 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 240 (accept_3_4 28 113 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 240 (Polychromatic418967fa.accept_7_6_1_2_1_230
  27 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 240 (accept_3_4 25 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 240 (Polychromatic418967fa.accept_13_10_9_6_1_1026 23 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 240 (accept_3_4 22 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 113 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 240 (accept_3_4 19 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 240 (Polychromatic418967fa.accept_21_18_8_9_1_2457 18 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 240 (accept_3_4 16 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 240 (Polychromatic418967fa.accept_13_2_9_6_1_501 15 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 240
  (Polychromatic418967fa.accept_13_1_9_6_1_146 14 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 240 (accept_3_4 13 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 240 (accept_3_4 10 113 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 240 (Polychromatic418967fa.accept_17_9_11_2_1_5894 9 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 240 (accept_3_4 7 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 240 (Polychromatic418967fa.accept_22_5_3_20_1_14389 5 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 240 (accept_3_4 4 113 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 113 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 240 (accept_3_4 1 113 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 240 (allA_succ_of_accept 111 112 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 111 112 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 112 240 2 55 56 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 112 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 109 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 112 240 4 27 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 112 240 (accept_3_5 107 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 112 240 2 53 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 112 240 (Polychromatic418967fa.accept_13_1_8_6_1_1016 105 112 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 112 240 8 13 14 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 112 240
  (Polychromatic418967fa.accept_11_4_2_9_1_496 103 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 112 240 2 51 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 112 240 (accept_3_5 101 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 112 240 4 25 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 112 240 (Polychromatic418967fa.accept_21_15_7_9_1_11550 99 112 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 112 240 2 49 56 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 112 240
  (Polychromatic418967fa.accept_9_7_4_6_1_273 97 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 112 240 16 6 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 112 240 (accept_3_5 95 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94
  112 240 2 47 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 93 112 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 93 112 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 112 240 4 23 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 112 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 91
  112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 112 240 2 45 56 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 112 240 (accept_3_5 89
  112 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 112 240 8 11 14 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 112 240
  (Polychromatic418967fa.accept_18_15_4_6_1_1763 87 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 112 240 2 43 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 112 240 (Polychromatic418967fa.accept_22_19_2_20_1_14362 85 112 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 112 240 4 21 28 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 112 240 (accept_3_5 83 112 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 112 240 2 41 56 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 112 240
  (Polychromatic418967fa.accept_11_4_2_9_1_496 81 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 112 240 16 5 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 112 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 79 112 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 112 240 2 39 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 112 240 (accept_3_5 77 112 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 76 112 240 4 19 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 112 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 75 112 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 112 240 2 37 56 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 112 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 73 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 112 240 8 9 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 112 240 (accept_3_5 71 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  112 240 2 35 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 112 240 (Polychromatic418967fa.accept_18_15_4_6_1_1763 69 112 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 112 240 4 17 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 112 240 (Polychromatic418967fa.accept_13_2_8_6_1_2390
  67 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 112 240 2 33 56 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 112 240
  (accept_3_5 65 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 112 240 16 4 7 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 112 240
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 63 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 112 240 2 31 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 112 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 112 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 112 240 4 15 28 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 112 240 (accept_3_5 59 112 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 112 240 2 29 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 112 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 57
  112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 240 8 7 14 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 55 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 112 240 2 27 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 112 240 (accept_3_5 53 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 112 240 4 13 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 112 240 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 112 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 240 2 25 56 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 240
  (Polychromatic418967fa.accept_17_15_10_2_1_2309 49 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 112 240 16 3 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 112 240 (accept_3_5 47 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 112 240 2 23 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 112 240 (Polychromatic418967fa.accept_21_3_7_9_1_8519 45 112 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 240 4 11 28 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 240
  (Polychromatic418967fa.accept_9_7_4_6_1_273 43 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 112 240 2 21 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 112 240 (accept_3_5 41 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 112 240 8 5 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 112 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 112 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 240 2 19 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 37
  112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 112 240 4 9 28 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 112 240 (accept_3_5 35
  112 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 112 240 2 17 56 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 112 240
  (Polychromatic418967fa.accept_18_15_4_6_1_1763 33 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 112 240 16 2 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 112 240 (Polychromatic418967fa.accept_21_10_7_9_1_11527 31 112 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 240 2 15 56 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 240 (accept_3_5 29 112 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 240 4 7 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 240 (Polychromatic418967fa.accept_13_1_8_6_1_1016
  27 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 240 2 13 56 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 240
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 240 8 3 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 112 240 (accept_3_5 23 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  112 240 2 11 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 112 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 112 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 240 4 5 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 19
  112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 112 240 2 9 56 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 112 240 (accept_3_5 17
  112 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 112 240 16 1 7 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 112 240
  (Polychromatic418967fa.accept_11_4_2_9_1_496 15 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 112 240 2 7 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 112 240 (Polychromatic418967fa.accept_21_13_7_9_1_2528 13 112 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 240 4 3 28 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 240 (accept_3_5 11 112 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 240 2 5 56 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 240
  (Polychromatic418967fa.accept_23_9_20_10_1_14388 9 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 112 240 8 1 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 112 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 112 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 240 2 3 56 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 240 (accept_3_5 5 112 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112 240 4 1 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 112 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 112 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 240 2 1 56 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 112 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 112
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 240 (allA_succ_of_accept 110 111 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 110 111 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 109 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 111 240 3 36 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 111 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 107 111 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 106 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 111 240 3 35 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 111 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 104 111 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 103 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 111 240 3 34 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 111 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 101 111 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 111 240 (Polychromatic418967fa.accept_9_1_3_6_1_70
  100 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 111 240 3 33 37 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 111 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 98 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 111 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 97 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 111 240 3 32 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 111 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 95
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 111 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 94 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 111 240 3 31 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 111 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 92 111 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 91
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 111 240 3 30 37 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 111 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 89 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 88 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 111 240 3 29 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 111 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 86
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 85 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 111 240 3 28 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 111 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 111 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 82
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 111 240 3 27 37 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 111 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 80 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 111 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 111 240 3 26 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 111 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 77
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 76 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 111 240 3 25 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 111 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 111 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 73
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 111 240 3 24 37 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 111 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 111 240 3 23 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 111 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 67 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 111 240 3 22 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 111 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 111 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 64
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 111 240 3 21 37 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 111 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 62 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 111 240 3 20 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 111 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 59
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 111 240 3 19 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 111 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 111 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 55
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 111 240 3 18 37 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 111 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 111 240 3 17 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 111 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 50
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 111 240 3 16 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 111 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 111 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 240 (Polychromatic418967fa.accept_7_4_6_2_1_451
  46 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 111 240 3 15 37 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 111 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 240 3 14 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 111 240 3 13 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 111 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 111 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 111 240 3 12 37 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 111 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 111 240 3 11 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 111 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 32
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 111 240 3 10 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 111 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 111 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 240 3 9 37 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 240 3 8 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 23
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 22 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 111 240 3 7 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 111 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 111 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 240 3 6 37 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 240 3 5 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 111 240 3 4 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 111 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 111 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 240 3 3 37 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 240 3 2 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 111 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 111 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 111 240 3 1 37 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 111 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 111 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 111 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 240 (allA_succ_of_accept 109 110 240 (accept_3_4 109 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 110 240 2 54 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 110 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 107 110 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 110 240 2 53 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 110 240 5 21 22 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 110 240 2 52 55 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 110 240
  (accept_3_4 103 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 110 240 2 51 55 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 110 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 101 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 110 240 10 10 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 110 240 (Polychromatic418967fa.accept_18_9_2_6_1_9322 99 110 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 110 240 2 49 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 110 240 (accept_3_4 97 110 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 110 240 2 48 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 110 240 5 19 22 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 110 240 2 47 55 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 93 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 110 240 2 46 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 110 240 (accept_3_4 91 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 240 10 9 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 89 110 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 240 2 44 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 87 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 240 2 43 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 110 240 5 17 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 110 240 2 42 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 110 240 (Polychromatic418967fa.accept_19_7_15_12_1_4800 83 110
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 240 2 41 55 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 81 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 240 10 8 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 240 (accept_3_4 79 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 240 2 39 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 77 110 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 240 2 38 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 110 240 5 15 22 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 110 240 2 37 55 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 110 240 (accept_3_4 73
  110 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 110 240 2 36 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 110 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 71 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 110 240 10 7 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 110 240 (Polychromatic418967fa.accept_25_19_10_15_1_14387 69 110 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 110 240 2 34 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 110 240 (accept_3_4 67 110 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 110 240 2 33 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 110 240 5 13 22 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 110 240 2 32 55 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 240
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 63 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 240 2 31 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 240 (accept_3_4 61 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 240 10 6 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 110 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 240 2 29 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 57 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 240 2 28 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 110 240 5 11 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 110 240 2 27 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 110 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 110 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 240 2 26 55 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 240
  (Polychromatic418967fa.accept_23_5_18_10_1_14318 51 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 110 240 10 5 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 110 240 (accept_3_4 49 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 240 2 24 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 240 (Polychromatic418967fa.accept_27_20_2_24_1_14386 47 110 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 240 2 23 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 110 240 5 9 22 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 110 240 2 22 55 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 110 240 (accept_3_4 43
  110 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 110 240 2 21 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 110 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 110 240 10 4 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 110 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 110 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 110 240 2 19 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 110 240 (accept_3_4 37 110 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 110 240 2 18 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 110 240 5 7 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 110 240 2 17 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 240
  (Polychromatic418967fa.accept_17_16_8_2_1_5890 33 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 240 2 16 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 240 (accept_3_4 31 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 240 10 3 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 240 (Polychromatic418967fa.accept_25_4_10_15_1_14385 29 110 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 240 2 14 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 240
  (Polychromatic418967fa.accept_17_10_8_2_1_8411 27 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 240 2 13 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 110 240 5 5 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 110 240 2 12 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 110 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 110 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 240 2 11 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 240 10 2 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 240 (accept_3_4 19 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 240 2 9 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 110 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 240 2 8 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 110 240 5 3 22 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 110 240 2 7 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 240 (accept_3_4 13 110 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 240 2 6 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 240 10 1 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 110 240 (Polychromatic418967fa.accept_18_9_2_6_1_9322 9 110 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 240 2 4 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 240 (accept_3_4 7 110 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110 240 2 3 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 110 240 5 1 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 110 240 2 2 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 3
  110 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 240 2 1 55 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 240 (accept_3_4 1
  110 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 240 (allA_succ_of_accept 108 109 240 (Polychromatic418967fa.accept_13_4_5_6_1_3201 108 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 240 (accept_3_5 107 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 106 109
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 240
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 105 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 240 (accept_3_5 104 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 103 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 109 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 102 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 240 (accept_3_5 101 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 240 (Polychromatic418967fa.accept_11_1_10_9_1_871 100 109
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 240
  (Polychromatic418967fa.accept_18_9_1_6_1_5301 99 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 240 (accept_3_5 98 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 97 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 96 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 240 (accept_3_5 95 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 94 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 93 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 240 (accept_3_5 92 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 240 (Polychromatic418967fa.accept_26_13_5_6_1_14384 91 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 240 (accept_3_5 89 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 88 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 240
  (Polychromatic418967fa.accept_31_25_16_23_1_14383 87 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 109 240 (accept_3_5 86 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 109 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 85 109 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 109 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 84 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 240 (accept_3_5 83 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 240 (Polychromatic418967fa.accept_7_5_4_2_1_235
  82 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 240
  (Polychromatic418967fa.accept_13_3_5_6_1_3192 81 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 240 (accept_3_5 80 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 79 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 240 (Polychromatic418967fa.accept_11_1_10_9_1_871 78 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 240 (accept_3_5 77 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 76 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 240 (accept_3_5 74 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 240 (Polychromatic418967fa.accept_19_16_14_12_1_6261 73 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 109 240 (Polychromatic418967fa.accept_23_3_17_10_1_9574 72 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 240 (accept_3_5 71 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 240 (Polychromatic418967fa.accept_9_7_1_6_1_261
  70 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 240 (accept_3_5 68 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 66 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 240 (accept_3_5 65 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 240 (Polychromatic418967fa.accept_13_12_5_6_1_1050 64 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 240
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 240 (accept_3_5 62 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 240 (Polychromatic418967fa.accept_17_9_7_2_1_2347 60 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 240 (accept_3_5 59 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 57 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 240 (accept_3_5 56 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 240 (accept_3_5 53 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 240
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 51 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 240 (accept_3_5 50 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 240 (accept_3_5 47 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 240 (Polychromatic418967fa.accept_17_12_7_2_1_4561 46 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 240
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 240 (accept_3_5 44 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 240 (Polychromatic418967fa.accept_13_3_5_6_1_3192 42 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 240 (accept_3_5 41 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 240 (accept_3_5 38 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 240 (Polychromatic418967fa.accept_13_11_5_6_1_519 37 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 240 (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 240 (accept_3_5 35 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 240 (accept_3_5 32 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 240 (accept_3_5 29 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 240 (Polychromatic418967fa.accept_19_9_14_12_1_7764 28 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 240 (accept_3_5 26 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 240 (Polychromatic418967fa.accept_13_11_5_6_1_519 24 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 240 (accept_3_5 23 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 240 (accept_3_5 20 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 240 (Polychromatic418967fa.accept_21_18_4_9_1_8484 18 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 240 (accept_3_5 17 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 240
  (Polychromatic418967fa.accept_17_15_7_2_1_2303 15 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 240 (accept_3_5 14 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 240 (accept_3_5 11 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 240 (Polychromatic418967fa.accept_13_10_5_6_1_1671 10 109 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 240
  (Polychromatic418967fa.accept_14_9_11_2_1_2501 9 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 240 (accept_3_5 8 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 240 (accept_3_5 5 109 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 109 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 240 (accept_3_5 2 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 240 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 109 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 240 (allA_succ_of_accept 107 108 240 (Polychromatic418967fa.accept_21_2_3_9_1_1317 107 108 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 108 240 2 53 54 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 108 240 3 35 36 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 108 240 4 26 27 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 108 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 103 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 240 6 17 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 240 (Polychromatic418967fa.accept_13_10_4_6_1_3224 101 108 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 108 240 4 25 27 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 108 240 3 33 36 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 108 240 2 49 54 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 108 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 97 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 240 12 8 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 108 240 (Polychromatic418967fa.accept_23_3_16_10_1_14356 95 108 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 108 240 2 47 54 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 108 240 3 31 36 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 108 240 4 23 27 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 240
  (Polychromatic418967fa.accept_21_7_3_9_1_5294 91 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 240 6 15 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 108 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 108 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 240 4 22 27 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 108 240 3 29 36 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 108 240 2 43 54 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 85 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 240 12 7 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 108 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 108 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 240 2 41 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 108 240 3 27 36 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 108 240 4 20 27 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 240
  (Polychromatic418967fa.accept_19_3_13_12_1_10525 79 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 108 240 6 13 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 108 240 (Polychromatic418967fa.accept_19_1_13_12_1_7748 77 108 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 240 4 19 27 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 108 240 3 25 36 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 108 240 2 37 54
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 240
  (Polychromatic418967fa.accept_19_16_13_12_1_7749 73 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 108 240 12 6 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 108 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 108 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 240 2 35 54 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 108 240 3 23 36 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 108 240 4 17 27 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 240
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 67 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 240 6 11 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 240 (Polychromatic418967fa.accept_21_2_3_9_1_1317 65 108 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 240 4 16 27 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 108 240 3 21 36 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 108 240 2 31 54 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 61 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 240 12 5 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 108 240 (Polychromatic418967fa.accept_13_7_4_6_1_3221 59 108 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 240 2 29 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 108 240 3 19 36 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 108 240 4 14 27 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 240 6 9 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 108 240 (Polychromatic418967fa.accept_23_7_16_10_1_14382 53 108 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 240 4 13 27 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 108 240 3 17 36 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 108 240 2 25 54 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 240
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 49 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 240 12 4 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 108 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 108 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 240 2 23 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 108 240 3 15 36 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 108 240 4 11 27 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 240 6 7 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 108 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 108 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 240 4 10 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 108 240 3 13 36 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 240 2 19 54 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 240
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 37 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 240 12 3 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 240 (Polychromatic418967fa.accept_13_9_4_6_1_1005 35 108 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 240 2 17 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 240 3 11 36 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 240 4 8 27 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 240
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 31 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 240 6 5 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 108 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 240 4 7 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 108 240 3 9 36 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 108 240 2 13 54 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 240
  (Polychromatic418967fa.accept_19_6_13_12_1_6220 25 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 108 240 12 2 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 108 240 (Polychromatic418967fa.accept_13_10_4_6_1_3224 23 108 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 240 2 11 54 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 240 3 7 36 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 240 4 5 27 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 240 6 3 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 240 (Polychromatic418967fa.accept_21_17_3_9_1_8524 17 108 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 240 4 4 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 240 3 5 36 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 240 2 7 54 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 240 12 1 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 240 (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 108 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 240 2 5 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 108 240 3 3 36 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 108 240 4 2 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 240 (Polychromatic418967fa.accept_13_7_4_6_1_3221 7
  108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 240 6 1 18 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 108 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 240 4 1 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 108 240 3 1 36 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 108 240 2 1 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 108 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 240 (allA_succ_of_accept 106 107 240 (accept_3_4 106 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 240 (Polychromatic418967fa.accept_13_1_3_6_1_158 105 107 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 104 107
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 240 (accept_3_4 103 107
  240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 102 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 101 107 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 240 (accept_3_4 100 107 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 240 (Polychromatic418967fa.accept_17_14_5_2_1_4559 99 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 240
  (Polychromatic418967fa.accept_11_10_8_9_1_492 98 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 240 (accept_3_4 97 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 240 (Polychromatic418967fa.accept_13_5_3_6_1_3278 96 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 95 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 240 (accept_3_4 94 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 93 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 92 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 240 (accept_3_4 91 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 240 (Polychromatic418967fa.accept_21_6_2_9_1_5292 90 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 240 (Polychromatic418967fa.accept_22_1_19_20_1_11377 89 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 240 (accept_3_4 88 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 240 (Polychromatic418967fa.accept_11_10_8_9_1_492 87 107
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 86 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 240 (accept_3_4 85 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 84 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 83 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 240 (accept_3_4 82 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 240 (Polychromatic418967fa.accept_14_11_9_2_1_6382 81 107 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 240
  (Polychromatic418967fa.accept_21_17_2_9_1_6867 80 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 240 (accept_3_4 79 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 240 (Polychromatic418967fa.accept_21_15_2_9_1_9962 78 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 77 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 240 (accept_3_4 76 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 240 (accept_3_4 73 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 240 (Polychromatic418967fa.accept_22_6_19_20_1_892 72 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 240 (Polychromatic418967fa.accept_17_3_5_2_1_14381 71 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 240 (accept_3_4 70 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 240 (Polychromatic418967fa.accept_18_15_17_6_1_4043 69 107
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 68 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 240 (accept_3_4 67 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 65 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 240 (accept_3_4 64 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 240 (Polychromatic418967fa.accept_14_7_9_2_1_2489 63 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 240
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 62 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 240 (accept_3_4 61 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 60 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 240 (accept_3_4 58 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 240 (accept_3_4 55 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 240 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 240 (Polychromatic418967fa.accept_13_1_3_6_1_158 53 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 240 (accept_3_4 52 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 240 (Polychromatic418967fa.accept_18_15_17_6_1_4043 51 107
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 240 (accept_3_4 49 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 240 (accept_3_4 46 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 240 (Polychromatic418967fa.accept_21_3_2_9_1_5338 45 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 240
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 44 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 240 (accept_3_4 43 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 240 (Polychromatic418967fa.accept_23_19_15_10_1_12865 42 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 240 (accept_3_4 40 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 107 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 240 (accept_3_4 37 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 240 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 240 (Polychromatic418967fa.accept_13_9_3_6_1_1661 35 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 240 (accept_3_4 34 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 240 (Polychromatic418967fa.accept_17_16_5_2_1_9724 33 107
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 240 (accept_3_4 31 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 240 (accept_3_4 28 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 240 (Polychromatic418967fa.accept_13_1_3_6_1_158 27 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 240
  (Polychromatic418967fa.accept_25_1_7_15_1_14380 26 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 107 240 (accept_3_4 25 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 107 240 (Polychromatic418967fa.accept_21_3_2_9_1_5338 24 107 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 107 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 240 (accept_3_4 22 107 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 21
  107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 240 (accept_3_4 19 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 240 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 240 (Polychromatic418967fa.accept_21_17_2_9_1_6867 17 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 240 (accept_3_4 16 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 240 (Polychromatic418967fa.accept_18_15_17_6_1_4043 15 107
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 240 (accept_3_4 13 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 240 (accept_3_4 10 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 240 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 240
  (Polychromatic418967fa.accept_22_8_19_20_1_8208 8 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 240 (accept_3_4 7 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 240 (Polychromatic418967fa.accept_21_6_2_9_1_5292 6 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 240 (accept_3_4 4 107 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 107 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 240 (accept_3_4 1 107 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 240 (allA_succ_of_accept 105 106 240 (Polychromatic418967fa.accept_13_1_2_6_1_515 105 106 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 106 240 2 52 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 106 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 103 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 106 240 2 51 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 106 240 (accept_3_5 101 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 106 240 2 50 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 106 240 (Polychromatic418967fa.accept_13_8_2_6_1_2385 99 106 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 106 240 2 49 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 106 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 97 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 106 240 2 48 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 106 240 (accept_3_5 95 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 106 240 2 47 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 106 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 93 106 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 106 240 2 46 53 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 106 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 91 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 106 240 2 45 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 106 240 (accept_3_5 89 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 106 240 2 44 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 106 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 106 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 106 240 2 43 53 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 106 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 85 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 106 240 2 42 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 106 240 (accept_3_5 83 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 106 240 2 41 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 106 240 (Polychromatic418967fa.accept_19_5_11_12_1_11765 81 106 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 106 240 2 40 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 106 240
  (Polychromatic418967fa.accept_11_2_7_9_1_890 79 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 106 240 2 39 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 106 240 (accept_3_5 77 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 106 240 2 38 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 106 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 75 106 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 240 2 37 53 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 73 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 240 2 36 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 240 (accept_3_5 71 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 240 2 35 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 106 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 240 2 34 53 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 67 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 106 240 2 33 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 240 (accept_3_5 65 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 240 2 32 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 240 (Polychromatic418967fa.accept_17_12_4_2_1_7116 63 106 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 240 2 31 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 240
  (Polychromatic418967fa.accept_13_9_2_6_1_514 61 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 240 2 30 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 240 (accept_3_5 59 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 240 2 29 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 106 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 240 2 28 53 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 240 2 27 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 240 (accept_3_5 53 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 240 2 26 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 240 (Polychromatic418967fa.accept_13_12_2_6_1_2396 51 106 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 240 2 25 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 240 2 24 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 240 (accept_3_5 47 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 240 2 23 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 106 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 240 2 22 53 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 240
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 43 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 240 2 21 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 240 (accept_3_5 41 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 240 2 20 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 106 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 240 2 19 53 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 240 2 18 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 240 (accept_3_5 35 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 240 2 17 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 240 (Polychromatic418967fa.accept_18_15_16_6_1_1751 33 106 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 240 2 16 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 240 2 15 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 240 (accept_3_5 29 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 240 2 14 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 106 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 240 2 13 53 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 240
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 25 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 240 2 12 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 240 (accept_3_5 23 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 240 2 11 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 106 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 240 2 10 53 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 240 2 9 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 106 240 (accept_3_5 17 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 106 240 2 8 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 106 240 (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 106 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 240 2 7 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 106 240 2 6 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 106 240 (accept_3_5 11 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 106 240 2 5 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 106 240 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 106 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 240 2 4 53 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 240
  (Polychromatic418967fa.accept_19_7_11_12_1_13190 7 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 106 240 2 3 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 106 240 (accept_3_5 5 106 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 106 240 2 2 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 106 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 106 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 240 2 1 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 1
  106 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 240 (allA_succ_of_accept 104 105 240 (Polychromatic418967fa.accept_19_9_10_12_1_6161 104 105 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 240
  (Polychromatic418967fa.accept_14_5_7_2_1_468 103 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 105 240 3 34 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 105 240 (Polychromatic418967fa.accept_18_11_15_6_1_2832 101 105 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 105 240 5 20 21 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 105 240 3 33 35 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 105 240
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 98 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 105 240 (Polychromatic418967fa.accept_19_2_10_12_1_3446 97 105 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 105 240 3 32 35 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 105 240 5 19 21 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 105 240
  (Polychromatic418967fa.accept_13_3_1_6_1_509 94 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 105 240 3 31 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 105 240 (Polychromatic418967fa.accept_22_4_17_20_1_9804 92 105 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 240
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 91 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 105 240 15 6 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 105 240 (Polychromatic418967fa.accept_14_5_7_2_1_468 89 105 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 240 (Polychromatic418967fa.accept_18_16_15_6_1_4039 88 105
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 105 240 3 29 35 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 105 240
  (Polychromatic418967fa.accept_13_8_1_6_1_997 86 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 105 240 5 17 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 84 105 240 3 28 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 105 240 (Polychromatic418967fa.accept_13_5_1_6_1_2367 83 105 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 240
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 82 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 105 240 3 27 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 80 105 240 5 16 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 105 240 (Polychromatic418967fa.accept_14_9_7_2_1_2483 79 105 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 105 240 3 26 35 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 105 240
  (Polychromatic418967fa.accept_18_5_15_6_1_3999 77 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 240 (Polychromatic418967fa.accept_18_4_15_6_1_3994 76 105 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 105 240 15 5 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 105 240 (Polychromatic418967fa.accept_13_9_1_6_1_510
  74 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 240
  (Polychromatic418967fa.accept_13_8_1_6_1_997 73 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 105 240 3 24 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 105 240 (Polychromatic418967fa.accept_18_17_15_6_1_1797 71 105 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 240 5 14 21 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 105 240 3 23 35 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 105 240
  (Polychromatic418967fa.accept_13_3_1_6_1_509 68 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 105 240 (Polychromatic418967fa.accept_13_2_1_6_1_2365 67 105 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 105 240 3 22 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 105 240 5 13 21 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 105 240
  (Polychromatic418967fa.accept_18_10_15_6_1_6621 64 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 105 240 3 21 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 105 240 (Polychromatic418967fa.accept_17_11_3_2_1_5867 62 105 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 240
  (Polychromatic418967fa.accept_13_9_1_6_1_510 61 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 105 240 15 4 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 105 240 (Polychromatic418967fa.accept_13_7_1_6_1_3287 59 105 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 240 (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 105
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 105 240 3 19 35 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 105 240
  (Polychromatic418967fa.accept_17_5_3_2_1_5847 56 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 105 240 5 11 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 105 240 3 18 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 105 240 (Polychromatic418967fa.accept_18_17_15_6_1_1797 53 105 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 240
  (Polychromatic418967fa.accept_17_1_3_2_1_5846 52 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 105 240 3 17 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 105 240 5 10 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 105 240 (Polychromatic418967fa.accept_19_11_10_12_1_2256 49 105 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 105 240 3 16 35 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 105 240
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 47 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 240 (Polychromatic418967fa.accept_13_7_1_6_1_3287 46 105 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 240 15 3 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 240 (Polychromatic418967fa.accept_13_5_1_6_1_2367
  44 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 240
  (Polychromatic418967fa.accept_23_20_13_10_1_12882 43 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 105 240 3 14 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 105 240 (Polychromatic418967fa.accept_13_2_1_6_1_2365 41 105 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 240 5 8 21 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 105 240 3 13 35 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 105 240
  (Polychromatic418967fa.accept_26_12_1_6_1_14379 38 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 105 240 (Polychromatic418967fa.accept_14_9_7_2_1_2483 37 105 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 105 240 3 12 35 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 105 240 5 7 21 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 240
  (Polychromatic418967fa.accept_13_8_1_6_1_997 34 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 105 240 3 11 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 105 240 (Polychromatic418967fa.accept_22_10_17_20_1_14378 32 105 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 240
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 31 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 105 240 15 2 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 105 240 (Polychromatic418967fa.accept_13_3_1_6_1_509 29 105 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 240 (Polychromatic418967fa.accept_13_2_1_6_1_2365 28 105
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 105 240 3 9 35 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 105 240
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 105 240 5 5 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 105 240 3 8 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 105 240 (Polychromatic418967fa.accept_14_9_7_2_1_2483 23 105 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 240 (Polychromatic418967fa.accept_13_9_1_6_1_510 22 105
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 240 3 7 35 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 105 240 5 4 21 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 240
  (Polychromatic418967fa.accept_14_5_7_2_1_468 19 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 105 240 3 6 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 105 240 (Polychromatic418967fa.accept_18_17_15_6_1_1797 17 105 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 240 (Polychromatic418967fa.accept_13_3_1_6_1_509
  16 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 240 15 1 7 16
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 240
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 240 (Polychromatic418967fa.accept_28_13_21_16_1_14377 13 105 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 240 3 4 35 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 240
  (Polychromatic418967fa.accept_17_11_3_2_1_5867 11 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 105 240 5 2 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 105 240 3 3 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 105 240 (Polychromatic418967fa.accept_13_8_1_6_1_997 8 105 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 240 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 105 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 240 3 2 35 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 105 240 5 1 21 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 240
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 4 105 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 240 3 1 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 240 (Polychromatic418967fa.accept_13_2_1_6_1_2365 2 105 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 240 (Polychromatic418967fa.accept_17_1_3_2_1_5846 1 105 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 240 (allA_succ_of_accept 103 104 240 (accept_3_4 103 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 240 2 51 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 101 104 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 240 4 25 26 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 99 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 240 2 49 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 240 (accept_3_4 97 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 240 8 12 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 95 104 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 240 2 47 52 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 93 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 240 4 23 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 104 240 (accept_3_4 91 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 240 2 45 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 89 104 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 240 8 11 13 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 87 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 240 2 43 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 240 (accept_3_4 85 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 240 4 21 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 83 104 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 240 2 41 52 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 240 8 10 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 240 (accept_3_4 79 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 240 2 39 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 240 (Polychromatic418967fa.accept_19_1_9_12_1_6207 77 104 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 240 4 19 26 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 75 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 240 2 37 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 240 (accept_3_4 73 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 240 8 9 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 104 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 104 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 240 2 35 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 240 (Polychromatic418967fa.accept_21_6_20_9_1_6943
  69 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 104 240 4 17 26 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 104 240
  (accept_3_4 67 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 104 240 2 33 52 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 104 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 104 240 8 8 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 104 240 (Polychromatic418967fa.accept_18_9_14_6_1_1790 63 104 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 104 240 2 31 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 104 240 (accept_3_4 61 104 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 104 240 4 15 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 104 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 104 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 240 2 29 52 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 240 8 7 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 104 240 (accept_3_4 55 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  104 240 2 27 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 104 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 104 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 240 4 13 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 240 (Polychromatic418967fa.accept_11_7_5_9_1_884
  51 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 104 240 2 25 52 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 104 240
  (accept_3_4 49 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 104 240 8 6 13 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 104 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 104 240 2 23 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 104 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 104 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 104 240 4 11 26 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 104 240 (accept_3_4 43 104 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 104 240 2 21 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 104 240 (Polychromatic418967fa.accept_19_3_9_12_1_6253
  41 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 240 8 5 13 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 240 2 19 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 240 (accept_3_4 37 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 240 4 9 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 104 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 104 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 240 2 17 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 240
  (Polychromatic418967fa.accept_19_14_9_12_1_9113 33 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 104 240 8 4 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 104 240 (accept_3_4 31 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 240 2 15 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 104 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 240 4 7 26 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 240
  (Polychromatic418967fa.accept_18_9_14_6_1_1790 27 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 240 2 13 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 240 (accept_3_4 25 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 240 8 3 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 104 240 (Polychromatic418967fa.accept_21_2_20_9_1_2507 23 104 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 240 2 11 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 21
  104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 104 240 4 5 26 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 104 240 (accept_3_4 19
  104 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 104 240 2 9 52 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 104 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 104 240 8 2 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 104 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 104 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 240 2 7 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 240 (accept_3_4 13 104 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 240 4 3 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 104 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 240 2 5 52 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 240
  (Polychromatic418967fa.accept_18_9_14_6_1_1790 9 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 240 8 1 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 240 (accept_3_4 7 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  240 2 3 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 240 (Polychromatic418967fa.accept_19_5_9_12_1_11778 5 104 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 240 4 1 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 104 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 104 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 240 2 1 52 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 240 (accept_3_4 1 104 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 104
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 240 (allA_succ_of_accept 102 103 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 102 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 240 (accept_3_5 101 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 103 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 100 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 240
  (Polychromatic418967fa.accept_18_9_13_6_1_877 99 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 240 (accept_3_5 98 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 97 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 240 (Polychromatic418967fa.accept_13_5_12_6_1_508 96 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 240 (accept_3_5 95 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 94 103 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 93 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 240 (accept_3_5 92 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 91 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 240 (Polychromatic418967fa.accept_11_2_4_9_1_484 90 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 240 (accept_3_5 89 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 88 103 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 87 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 240 (accept_3_5 86 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 240 (Polychromatic418967fa.accept_13_7_12_6_1_1039 85 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 84 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 240 (accept_3_5 83 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 82 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 81 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 240 (accept_3_5 80 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 79 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 240 (Polychromatic418967fa.accept_21_15_19_9_1_2504 78 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 240 (accept_3_5 77 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 240 (Polychromatic418967fa.accept_29_18_16_8_1_14376 76
  103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 75 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 240 (accept_3_5 74 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 73 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 240 (Polychromatic418967fa.accept_13_7_12_6_1_1039 72 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 240 (accept_3_5 71 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 103 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 240
  (Polychromatic418967fa.accept_32_5_7_16_1_14375 69 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 103 240 (accept_3_5 68 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 103 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 103 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 103 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 240 (accept_3_5 65 103 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 64
  103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 240
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 63 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 240 (accept_3_5 62 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 240 (accept_3_5 59 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 240 (Polychromatic418967fa.accept_19_1_8_12_1_6149 58 103 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 240 (accept_3_5 56 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 240 (Polychromatic418967fa.accept_13_2_12_6_1_2394 54 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 240 (accept_3_5 53 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 103 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 240
  (Polychromatic418967fa.accept_22_7_15_20_1_14374 51 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 103 240 (accept_3_5 50 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 103 240 (Polychromatic418967fa.accept_13_10_12_6_1_991 49 103 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 103 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 240 (accept_3_5 47 103 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 240 (Polychromatic418967fa.accept_7_4_5_2_1_243
  46 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 240 (accept_3_5 44 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 240 (Polychromatic418967fa.accept_19_4_8_12_1_4757 42 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 240 (accept_3_5 41 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 240 (Polychromatic418967fa.accept_17_6_1_2_1_10823 40 103
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 240 (accept_3_5 38 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 240 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 240 (accept_3_5 35 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 103 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 240
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 33 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 240 (accept_3_5 32 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 240 (accept_3_5 29 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 240
  (Polychromatic418967fa.accept_18_9_13_6_1_877 27 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 240 (accept_3_5 26 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 240 (accept_3_5 23 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 240 (Polychromatic418967fa.accept_23_22_11_10_1_6063 22 103 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 240 (accept_3_5 20 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 240 (accept_3_5 17 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 240
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 15 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 240 (accept_3_5 14 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 240 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 240 (accept_3_5 11 103 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 240
  (Polychromatic418967fa.accept_18_9_13_6_1_877 9 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 240 (accept_3_5 8 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 240 (Polychromatic418967fa.accept_17_6_1_2_1_10823 6 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 240 (accept_3_5 5 103 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 103 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 240 (accept_3_5 2 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 103 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 240 (allA_succ_of_accept 101 102 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 101 102 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 102 240 2 50 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 102 240 3 33 34 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 102 240 2 49 51 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 97 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 102 240 6 16 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 102 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 95 102 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 102 240 2 47 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 102 240 3 31 34 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 102 240 2 46 51 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 91 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 240 6 15 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 102 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 102 240 2 44 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 102 240 3 29 34 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 102 240 2 43 51 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 85 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 240 6 14 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 102 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 240 2 41 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 102 240 3 27 34 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 102 240 2 40 51 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 79 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 240 6 13 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 77 102 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 240 2 38 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 102 240 3 25 34 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 102 240 2 37 51 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 73 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 240 6 12 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 71 102 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 240 2 35 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 102 240 3 23 34 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 102 240 2 34 51 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 240 6 11 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 102 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 240 2 32 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 102 240 3 21 34 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 102 240 2 31 51 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 61 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 240 6 10 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 59 102 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 240 2 29 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 102 240 3 19 34 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 102 240 2 28 51 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 55 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 240 6 9 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 102 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 53 102 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 240 2 26 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 102 240 3 17 34 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 102 240 2 25 51 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 240 6 8 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 102 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 102 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 240 2 23 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 102 240 3 15 34 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 102 240 2 22 51 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 240 6 7 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 102 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 102 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 240 2 20 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 102 240 3 13 34 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 102 240 2 19 51 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 240 6 6 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 102 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 102 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 240 2 17 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 102 240 3 11 34 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 102 240 2 16 51 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 240 6 5 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 102 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 102 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 240 2 14 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 102 240 3 9 34 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 102 240 2 13 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 240 6 4 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 102 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 102 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 240 2 11 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 240 3 7 34 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 240 2 10 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 240 6 3 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 102 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 240 2 8 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 240 3 5 34 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 240 2 7 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 240 6 2 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 102 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 102 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 240 2 5 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 102 240 3 3 34 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 102 240 2 4 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7
  102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 240 6 1 17 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 102 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 102 240 2 2 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 102 240 3 1 34 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 102 240 2 1 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 102 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 102 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 240 (allA_succ_of_accept 100 101 240 (accept_3_4 100 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 99 101 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 98 101 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 240 (accept_3_4 97 101 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 240 (Polychromatic418967fa.accept_7_5_3_2_1_249
  96 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 95 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 240 (accept_3_4 94 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 93 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 92 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 240 (accept_3_4 91 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 89 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 240 (accept_3_4 88 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 240 (Polychromatic418967fa.accept_13_9_10_6_1_1028 87 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 86 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 240 (accept_3_4 85 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 240 (accept_3_4 82 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 240 (Polychromatic418967fa.accept_11_4_2_9_1_496 81 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 80 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 240 (accept_3_4 79 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 77 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 101 240 (accept_3_4 76 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 101 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 101 240 (Polychromatic418967fa.accept_13_9_10_6_1_1028 74 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 240 (accept_3_4 73 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 240 (Polychromatic418967fa.accept_19_15_6_12_1_7746 72 101
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 240 (accept_3_4 70 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 240 (accept_3_4 67 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 240
  (Polychromatic418967fa.accept_17_14_16_2_1_4553 65 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 101 240 (accept_3_4 64 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 101 240 (Polychromatic418967fa.accept_32_31_5_16_1_14373 63 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 240 (Polychromatic418967fa.accept_7_6_3_2_1_461
  62 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 240 (accept_3_4 61
  101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 240
  (Polychromatic418967fa.accept_21_18_17_9_1_6897 60 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 240 (accept_3_4 58 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 240
  (Polychromatic418967fa.accept_13_4_10_6_1_989 56 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 240 (accept_3_4 55 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 240 (accept_3_4 52 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 240 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 240 (accept_3_4 49 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 240 (accept_3_4 46 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 240 (Polychromatic418967fa.accept_21_3_17_9_1_9958 45 101 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 240 (accept_3_4 43 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 240 (Polychromatic418967fa.accept_13_3_10_6_1_2382 42 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 240 (accept_3_4 40 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 240
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 38 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 101 240 (accept_3_4 37 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 101 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 101 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 101 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 240 (accept_3_4 34 101 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 240 (Polychromatic418967fa.accept_7_5_3_2_1_249
  33 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 240 (accept_3_4 31 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 240 (accept_3_4 28 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 240 (accept_3_4 25 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 240 (Polychromatic418967fa.accept_21_3_17_9_1_9958 24 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 240 (accept_3_4 22 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 240 (accept_3_4 19 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 240 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 240 (accept_3_4 16 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 240 (accept_3_4 13 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 240 (Polychromatic418967fa.accept_22_11_13_20_1_14372 11 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 240 (accept_3_4 10 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 240 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 101
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 240 (accept_3_4 7 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 240 (accept_3_4 4 101 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 101 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 240
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 2 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 240 (accept_3_4 1 101 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_240_segment_000)))))))))))))))))))))))))))))))))))))))))))))


