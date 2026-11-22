-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch188_Segment000
-- name    : Polychromatic418967fa_Branch188_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:28:09.710282+00:00
-- url     : https://prove2.me/theorems/4d9c957b-0d41-40c1-885a-f9253276727e
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

def Polychromatic418967fa.branch_188_segment_000 : allB 140 188 :=
  allB_succ' 50 139 188 (Eq.refl Bool.true) (allA_of_3_0 50 139 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  51 138 188 (Eq.refl Bool.true) (allA_succ_of_gcd 50 138 188 2 25 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 188 (accept_3_2 49 138 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 138 188 2 24 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 138 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 138 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 188 2 23 69 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 188 2 22 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 188 (accept_3_2 43 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 188 2 21 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 138 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 188 2 20 69 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 188 2 19 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 188 (accept_3_2 37 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 188 2 18 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 188 (Polychromatic418967fa.accept_15_5_3_8_1_748 35 138 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 188 2 17 69 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 188
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 188 2 16 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 188 (accept_3_2 31 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 188 2 15 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 138 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 188 2 14 69 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 188
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 188 2 13 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 188 (accept_3_2 25 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 188 2 12 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 138 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 188 2 11 69 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 188 2 10 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 188 (accept_3_2 19 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 188 2 9 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 188 (Polychromatic418967fa.accept_22_17_6_12_1_5923 17 138 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 188 2 8 69 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 138 188 2 7 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 138 188 (accept_3_2 13 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  138 188 2 6 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 138 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 138 188 2 5 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 138 188 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 138 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 188 2 4 69 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 188 (accept_3_2 7 138 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 188 2 3 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 138 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 188 2 2 69 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 138 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 138 188 2 1 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 138 188 (accept_3_2 1 138 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  188))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 137 188 (Eq.refl Bool.true) (allA_succ_of_accept
  51 137 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 188 (accept_3_2 49 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 137 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 188
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 188 (accept_3_2 46 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 188 (accept_3_2 43 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 137 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 188 (accept_3_2 40 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 188 (accept_3_2 37 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 188 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 137 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 188
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 188 (accept_3_2 34 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 188 (accept_3_2 31 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 137 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 188
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 188 (accept_3_2 28 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 188 (accept_3_2 25 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 137 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 188 (accept_3_2 22 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 188 (Polychromatic418967fa.accept_16_4_9_12_1_4829 20 137 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 188 (accept_3_2 19 137 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 188 (Polychromatic418967fa.accept_16_2_9_12_1_46 18 137
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 188 (accept_3_2 16 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 188 (accept_3_2 13 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 137 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 188
  (Polychromatic418967fa.accept_19_11_4_17_1_2617 11 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 137 188 (accept_3_2 10 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 137 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 188 (Polychromatic418967fa.accept_16_8_9_12_1_1737 8 137
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 188 (accept_3_2 7 137 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 188
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 188 (accept_3_2 4 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 137 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 188 (accept_3_2 1 137 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 188)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 136 188
  (Eq.refl Bool.true) (allA_of_3_0 53 136 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 135 188 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 135 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 188 (accept_3_2 52 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 135 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 135 188 (accept_3_2 49 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 135 188 (Polychromatic418967fa.accept_19_10_2_17_1_675 48 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 188 (accept_3_2 46 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 135 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 188
  (Polychromatic418967fa.accept_21_2_9_20_1_9260 44 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 188 (accept_3_2 43 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 135 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 135 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 188 (accept_3_2 40 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 135 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 188 (accept_3_2 37 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 135 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 188 (accept_3_2 34 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 188 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 135 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 188 (accept_3_2 31 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 135 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 135 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 188 (accept_3_2 28 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 135 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 188
  (Polychromatic418967fa.accept_19_7_2_17_1_9426 26 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 188 (accept_3_2 25 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 135 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 188 (accept_3_2 22 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 188 (Polychromatic418967fa.accept_16_5_7_12_1_7206 21 135 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 188
  (Polychromatic418967fa.accept_16_4_7_12_1_2734 20 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 188 (accept_3_2 19 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 188 (accept_3_2 16 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 135 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 188
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 14 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 188 (accept_3_2 13 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 188 (accept_3_2 10 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 188 (Polychromatic418967fa.accept_19_9_2_17_1_10805 9 135 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 188 (accept_3_2 7 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 188 (accept_3_2 4 135 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 135 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 188
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 188 (accept_3_2 1 135 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 134 188 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 134 188 2 27 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 134 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 134 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 188 2 26 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 51
  134 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 134 188 2 25 67 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 134 188 (accept_3_2 49
  134 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 134 188 2 24 67 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 134 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 134 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 134 188 2 23 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 134 188 (Polychromatic418967fa.accept_20_5_14_8_1_6391 45 134 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 134 188 2 22 67 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 134 188 (accept_3_2 43 134 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 134 188 2 21 67 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 134 188
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 134 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 134 188 2 20 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 134 188 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 134 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 134 188 2 19 67 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 134 188 (accept_3_2 37 134 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 134 188 2 18 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 134 188 (Polychromatic418967fa.accept_12_11_2_8_1_511
  35 134 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 188 2 17 67 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 134 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 188 2 16 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 188 (accept_3_2 31 134 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 188 2 15 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 188 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 134 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 188 2 14 67 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 188
  (Polychromatic418967fa.accept_22_5_2_12_1_10800 27 134 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 134 188 2 13 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 134 188 (accept_3_2 25 134 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 188 2 12 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 134 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 188 2 11 67 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 188
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 134 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 188 2 10 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 188 (accept_3_2 19 134 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 188 2 9 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 134 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 134 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 188 2 8 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 188 (Polychromatic418967fa.accept_13_2_4_6_1_2356
  15 134 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 188 2 7 67 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 188
  (accept_3_2 13 134 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 188 2 6 67 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 188
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 134 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 134 188 2 5 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 134 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 134 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 188 2 4 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 188 (accept_3_2 7 134 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 134 188 2 3 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 134 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 134 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 188 2 2 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 188 (Polychromatic418967fa.accept_11_3_2_1_1_994 3
  134 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 188 2 1 67 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 188 (accept_3_2 1
  134 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 133 188 (Eq.refl Bool.true) (allA_of_3_0 56
  133 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 132 188 (Eq.refl Bool.true) (allA_succ_of_gcd 56 132
  188 4 14 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55
  132 188 (accept_3_2 55 132 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 132 188 2 27 66 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 132 188
  (Polychromatic418967fa.accept_13_1_2_6_1_515 53 132 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 132 188 4 13 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 132 188 (Polychromatic418967fa.accept_13_12_2_6_1_2396 51 132 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 132 188 2 25 66 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 188 (accept_3_2 49 132 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 132 188 4 12 33 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 132 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 132 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 188 2 23 66 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 132 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 132 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 188 4 11 33 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 188 (accept_3_2 43 132 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 132 188 2 21 66 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 132 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 41
  132 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 188 4 10 33 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 188
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 132 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 188 2 19 66 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 188 (accept_3_2 37 132 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 188 4 9 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 132 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 188 2 17 66 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 188 (Polychromatic418967fa.accept_15_3_12_8_1_738
  33 132 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 188 4 8 33 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 188
  (accept_3_2 31 132 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 188 2 15 66 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 132 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 188 4 7 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 132 188 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 132 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 188 2 13 66 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 188 (accept_3_2 25 132 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 188 4 6 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 132 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 188 2 11 66 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 188
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 132 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 188 4 5 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 132 188 (accept_3_2 19 132 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  132 188 2 9 66 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 132 188 (Polychromatic418967fa.accept_13_4_2_6_1_1043 17 132 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 132 188 4 4 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 132 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 132 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 188 2 7 66 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 188 (accept_3_2 13 132 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 188 4 3 33 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 132 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 188 2 5 66 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 132 188 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 132 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 188 4 2 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 188 (accept_3_2 7 132 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 132 188 2 3 66 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 132 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 132 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 188 4 1 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 132 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  132 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 188 2 1 66 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 188 (accept_3_2 1
  132 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 131 188 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 131 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 131 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 131 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 188 (accept_3_2 55 131 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 188 (Polychromatic418967fa.accept_13_2_1_6_1_2365
  54 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 188 (accept_3_2 52 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 131 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 188 (accept_3_2 49 131 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 131 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 188
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 188 (accept_3_2 46 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 188 (Polychromatic418967fa.accept_13_5_1_6_1_2367 44 131 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 188 (accept_3_2 43 131 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 131 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 188
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 41 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 188 (accept_3_2 40 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 131 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 188 (accept_3_2 37 131 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 131 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 188
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 188 (accept_3_2 34 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 131 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 188 (accept_3_2 31 131 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 131 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 188 (accept_3_2 28 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 131 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 188 (accept_3_2 25 131 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 131 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 188
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 188 (accept_3_2 22 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 131 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 188 (accept_3_2 19 131 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 131 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 188
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 17 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 188 (accept_3_2 16 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 131 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 188 (accept_3_2 13 131 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 131 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 188 (accept_3_2 10 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 131 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 188 (accept_3_2 7 131 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 131 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 188
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 188 (accept_3_2 4 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 131 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 188 (accept_3_2 1 131 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 130
  188 (Eq.refl Bool.true) (allA_of_3_0 59 130 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 129 188
  (Eq.refl Bool.true) (allA_succ_of_accept 59 129 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 129 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 188 (accept_3_2 58 129 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 188 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 129
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 129 188 (accept_3_2 55 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 129 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 129 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 188 (accept_3_2 52 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 129 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 188 (accept_3_2 49 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 129 188 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 129 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 188 (accept_3_2 46 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 129 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 188 (accept_3_2 43 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 129 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 129 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 188 (accept_3_2 40 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 129 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 188 (accept_3_2 37 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 188 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 188 (accept_3_2 34 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 129 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 188 (accept_3_2 31 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 188 (accept_3_2 28 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 188 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 129 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 188
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 188 (accept_3_2 25 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 188 (accept_3_2 22 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 129 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 188 (accept_3_2 19 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 188 (accept_3_2 16 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 129 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 188 (accept_3_2 13 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 188 (Polychromatic418967fa.accept_18_12_3_8_1_6817 12 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 188 (accept_3_2 10 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 129 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 188
  (Polychromatic418967fa.accept_16_8_1_12_1_984 8 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 188 (accept_3_2 7 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 188 (accept_3_2 4 129 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 188 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 129 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 188 (accept_3_2 1 129 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 128 188 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 128 188 4 15 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 128 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 188 2 29 64 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 188 4 14 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 128 188 (accept_3_2 55 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 128 188 2 27 64 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 128 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 128 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 188 4 13 32 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 188
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 128 188 2 25 64 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 128 188 (accept_3_2 49 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 188 4 12 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 188 (Polychromatic418967fa.accept_13_8_11_6_1_1035 47 128 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 188 2 23 64 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 188 4 11 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 188 (accept_3_2 43 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 188 2 21 64 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 128 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 188 4 10 32 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 188 2 19 64 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 188 (accept_3_2 37 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 188 4 9 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 128 188 (Polychromatic418967fa.accept_18_17_2_8_1_6800 35 128 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 188 2 17 64 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 33
  128 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 128 188 4 8 32 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 128 188 (accept_3_2 31
  128 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 128 188 2 15 64 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 128 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 128 188 4 7 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 128 188 (Polychromatic418967fa.accept_17_10_9_1_1_7062 27 128 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 128 188 2 13 64 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 128 188 (accept_3_2 25 128 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 128 188 4 6 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 128 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 128 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 188 2 11 64 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 188
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 188 4 5 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 128 188 (accept_3_2 19 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  128 188 2 9 64 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 128 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 128 188 4 4 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 128 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 128 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 188 2 7 64 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 188 (accept_3_2 13 128 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 188 4 3 32 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 128 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 128 188 2 5 64 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 128 188 (Polychromatic418967fa.accept_19_9_14_17_1_2613 9 128 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 188 4 2 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 188 (accept_3_2 7 128 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 128 188 2 3 64 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 128 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 128 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 188 4 1 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 3
  128 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 188 2 1 64 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 188 (accept_3_2 1
  128 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 127 188 (Eq.refl Bool.true)
  (allA_of_3_0 62 127 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 126 188 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 126 188 2 31 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 126 188 (accept_3_2 61 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 188 2 30 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 188 (Polychromatic418967fa.accept_13_7_9_6_1_148 59 126 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 188 2 29 63 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 126 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 126 188 2 28 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 126 188 (accept_3_2 55 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 188 2 27 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 188 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 126 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 188 2 26 63 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 126 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 126 188 2 25 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 126 188 (accept_3_2 49 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 188 2 24 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 188 (Polychromatic418967fa.accept_15_2_6_8_1_754 47 126 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 188 2 23 63 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 188 2 22 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 188 (accept_3_2 43 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 188 2 21 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 188 (Polychromatic418967fa.accept_13_2_9_6_1_501 41 126 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 188 2 20 63 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 188
  (Polychromatic418967fa.accept_11_6_5_1_1_586 39 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 188 2 19 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 188 (accept_3_2 37 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 188 2 18 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 188 (Polychromatic418967fa.accept_23_12_11_4_1_5708 35 126 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 188 2 17 63 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 188
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 188 2 16 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 188 (accept_3_2 31 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 188 2 15 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 188 (Polychromatic418967fa.accept_13_3_9_6_1_502 29 126 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 188 2 14 63 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 188 2 13 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 188 (accept_3_2 25 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 188 2 12 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 188 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 126 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 188 2 11 63 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 188 2 10 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 188 (accept_3_2 19 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 188 2 9 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 188 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 126 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 188 2 8 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 188 (Polychromatic418967fa.accept_12_3_6_8_1_969
  15 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 188 2 7 63 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 188
  (accept_3_2 13 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 188 2 6 63 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 188
  (Polychromatic418967fa.accept_17_11_7_1_1_7023 11 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 188 2 5 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 126 188 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 126 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 188 2 4 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 188 (accept_3_2 7 126 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 126 188 2 3 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 126 188 (Polychromatic418967fa.accept_19_5_12_17_1_8089 5 126 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 188 2 2 63 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 126 188
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 126 188 2 1 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 126 188 (accept_3_2 1 126 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 125 188 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 125 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 125 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 125
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 188 (accept_3_2 61 125
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 188
  (Polychromatic418967fa.accept_23_14_10_4_1_10804 60 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 125 188 (Polychromatic418967fa.accept_15_14_5_8_1_3175 59 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 188 (accept_3_2 58 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 125 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 188
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 125 188 (accept_3_2 55 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 125 188 (Polychromatic418967fa.accept_13_2_8_6_1_2390 54 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 125 188 (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 188 (accept_3_2 52 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 125 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 188 (accept_3_2 49 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 188 (Polychromatic418967fa.accept_15_3_5_8_1_1387 48 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 188 (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 188 (accept_3_2 46 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 125 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 188
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 44 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 188 (accept_3_2 43 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 125 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 188 (accept_3_2 40 125 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 188 (accept_3_2 37 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 188 (Polychromatic418967fa.accept_16_4_13_12_1_1740 36 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 188 (Polychromatic418967fa.accept_14_7_13_6_1_1177 35 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 188 (accept_3_2 34 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 188
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 188 (accept_3_2 31 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 188 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 188 (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 188 (accept_3_2 28 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 125 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 188 (accept_3_2 25 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 188 (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 188 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 188 (accept_3_2 22 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 188
  (Polychromatic418967fa.accept_16_4_13_12_1_1740 20 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 125 188 (accept_3_2 19 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 125 188 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 125 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 125 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 188 (accept_3_2 16 125 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 188 (accept_3_2 13 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 188 (Polychromatic418967fa.accept_13_11_8_6_1_1023 11 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 188 (accept_3_2 10 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 188
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 188 (accept_3_2 7 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 188 (Polychromatic418967fa.accept_19_6_11_17_1_2611 6 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 188 (Polychromatic418967fa.accept_14_5_13_6_1_3574 5 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 188 (accept_3_2 4 125 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 125 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 188
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 188 (accept_3_2 1 125 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 124 188 (Eq.refl Bool.true)
  (allA_of_3_0 65 124 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 123 188 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 123 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 123 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 188 (accept_3_2 64 123 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 123 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 188
  (Polychromatic418967fa.accept_27_8_15_26_1_10803 62 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 123 188 (accept_3_2 61 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 123 188 (Polychromatic418967fa.accept_25_10_23_13_1_10802 60 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 59
  123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 188 (accept_3_2 58
  123 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 123 188
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 123 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 123 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 188 (accept_3_2 55 123 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 123 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 188 (accept_3_2 52
  123 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 123 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 123 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 123 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 188 (accept_3_2 49 123 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 123 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 188 (accept_3_2 46
  123 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 123 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 123 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 123 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 188 (accept_3_2 43 123 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 123 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 123 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 188 (accept_3_2 40 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 188 (accept_3_2 37 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 123 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 188 (accept_3_2 34 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 188 (accept_3_2 31 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 123 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 188 (accept_3_2 28 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 188 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 188 (accept_3_2 25 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 123 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 188 (accept_3_2 22 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 188 (accept_3_2 19 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 123 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 188 (accept_3_2 16 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 188 (accept_3_2 13 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 123 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 188 (accept_3_2 10 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 188 (Polychromatic418967fa.accept_16_8_11_12_1_962 8 123 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 188 (accept_3_2 7 123 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 123 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 188 (accept_3_2 4 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 123 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 188 (accept_3_2 1 123 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  67 122 188 (Eq.refl Bool.true) (allA_succ_of_gcd 66 122 188 2 33 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 122 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 65
  122 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 188 2 32 61 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 188
  (Polychromatic418967fa.accept_13_11_5_6_1_519 63 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 188 2 31 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 188 (accept_3_2 61 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 188 2 30 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 122 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 188 2 29 61 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 188 2 28 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 188 (accept_3_2 55 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 188 2 27 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 122 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 188 2 26 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 188 2 25 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 188 (accept_3_2 49 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 188 2 24 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 122 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 188 2 23 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 188
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 188 2 22 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 188 (accept_3_2 43 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 188 2 21 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 122 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 188 2 20 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 188 2 19 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 188 (accept_3_2 37 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 188 2 18 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 122 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 188 2 17 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 188
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 188 2 16 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 188 (accept_3_2 31 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 188 2 15 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 122 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 188 2 14 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 188
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 188 2 13 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 188 (accept_3_2 25 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 188 2 12 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 122 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 188 2 11 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 188 2 10 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 188 (accept_3_2 19 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 188 2 9 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 122 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 188 2 8 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  122 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 188 2 7 61 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 188 (accept_3_2 13
  122 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 188 2 6 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 122 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 188 2 5 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 122 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 188 2 4 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 188 (accept_3_2 7 122 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 188 2 3 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 122 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 188 2 2 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 3
  122 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 188 2 1 61 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 188 (accept_3_2 1
  122 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 121 188 (Eq.refl Bool.true)
  (allA_of_3_0 68 121 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 120 188 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 120 188 4 17 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 120 188 (accept_3_2 67 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 188 2 33 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 120 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 120 188 4 16 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 120 188
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 63 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 120 188 2 31 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 120 188 (accept_3_2 61 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 188 4 15 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 120 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 188 2 29 60 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 188
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 120 188 4 14 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 120 188 (accept_3_2 55 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 188 2 27 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 188 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 120 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 188 4 13 30 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 188
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 120 188 2 25 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 120 188 (accept_3_2 49 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 188 4 12 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 120 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 188 2 23 60 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 120 188
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 45 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 120 188 4 11 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 120 188 (accept_3_2 43 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 188 2 21 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 120 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 188 4 10 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 188
  (Polychromatic418967fa.accept_16_7_8_12_1_4902 39 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 120 188 2 19 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 120 188 (accept_3_2 37 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 188 4 9 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 120 188 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 120 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 188 2 17 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 33
  120 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 188 4 8 30 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 188 (accept_3_2 31
  120 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 188 2 15 60 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 188 4 7 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 120 188 (Polychromatic418967fa.accept_13_1_3_6_1_158 27 120 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 188 2 13 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 188 (accept_3_2 25 120 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 188 4 6 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 120 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 188 2 11 60 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 188
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 188 4 5 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 188 (accept_3_2 19 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  120 188 2 9 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 120 188 (Polychromatic418967fa.accept_16_1_8_12_1_405 17 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 120 188 4 4 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 120 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 120 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 188 2 7 60 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 188 (accept_3_2 13 120 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 188 4 3 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 188 2 5 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 120 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 120 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 188 4 2 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 188 (accept_3_2 7 120 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 120 188 2 3 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 120 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 120 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 188 4 1 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 188 (Polychromatic418967fa.accept_16_3_8_12_1_2736
  3 120 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 188 2 1 60 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 188 (accept_3_2 1
  120 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 119 188 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 119 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 119 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 119 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 188 (accept_3_2 67 119 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 119 188 (Polychromatic418967fa.accept_9_3_2_8_1_108
  66 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 188
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 65 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 119 188 (accept_3_2 64 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 119 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 119 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 188 (accept_3_2 61 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 119 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 188
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 188 (accept_3_2 58 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 119 188 (Polychromatic418967fa.accept_13_4_2_6_1_1043 56 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 188 (accept_3_2 55 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 119
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 188
  (Polychromatic418967fa.accept_13_1_2_6_1_515 53 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 188 (accept_3_2 52 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 119 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 188 (accept_3_2 49 119 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 188
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 188 (accept_3_2 46 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 188 (accept_3_2 43 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 119 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 119 188 (accept_3_2 40 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 119 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 119 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 188 (accept_3_2 37 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 188 (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 119
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 188
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 188 (accept_3_2 34 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 119 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 188 (accept_3_2 31 119 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 188
  (Polychromatic418967fa.accept_14_1_7_6_1_3604 29 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 188 (accept_3_2 28 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 188 (accept_3_2 25 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 119 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 188 (accept_3_2 22 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 188 (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 188 (accept_3_2 19 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 188 (Polychromatic418967fa.accept_16_2_7_12_1_3793 18 119
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 188
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 188 (accept_3_2 16 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 119 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 188 (accept_3_2 13 119 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 188
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 188 (accept_3_2 10 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 188 (Polychromatic418967fa.accept_13_8_2_6_1_2385 8 119 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 188 (accept_3_2 7 119 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 119 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 188 (accept_3_2 4 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 119 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 188 (accept_3_2 1 119 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119 188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 71 118 188 (Eq.refl Bool.true) (allA_of_3_0 71 118 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 72 117 188 (Eq.refl Bool.true) (allA_succ_of_accept 71 117 188 (Polychromatic418967fa.accept_6_5_3_2_1_68
  71 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 188 (accept_3_2 70
  117 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 188
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 117 188 (Polychromatic418967fa.accept_16_4_5_12_1_2749 68 117 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 188 (accept_3_2 67 117 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 117 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 188 (accept_3_2 64 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 117 188 (Polychromatic418967fa.accept_15_3_12_8_1_738 63 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 188 (Polychromatic418967fa.accept_19_5_3_17_1_6557 62 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 188 (accept_3_2 61 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 117 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 188 (accept_3_2 58 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 117 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 117 188 (Polychromatic418967fa.accept_15_11_12_8_1_739 56 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 188 (accept_3_2 55 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 117
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 188 (accept_3_2 52 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 117 188 (Polychromatic418967fa.accept_20_11_17_8_1_4903 51 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 117 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 188 (accept_3_2 49 117 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 188 (Polychromatic418967fa.accept_15_3_12_8_1_738 48 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 188 (accept_3_2 46 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 188 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 188 (Polychromatic418967fa.accept_19_6_3_17_1_9472 44 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 188 (accept_3_2 43 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 117
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 188 (accept_3_2 40 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 188 (Polychromatic418967fa.accept_22_16_7_12_1_7630 38 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 188 (accept_3_2 37 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 117 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 188 (accept_3_2 34 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 117 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 188 (accept_3_2 31 117 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 188 (accept_3_2 28 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 188 (Polychromatic418967fa.accept_14_13_5_6_1_2747 27 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 188 (Polychromatic418967fa.accept_15_11_12_8_1_739 26 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 188 (accept_3_2 25 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 188 (Polychromatic418967fa.accept_16_8_5_12_1_3812 24 117
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 188 (accept_3_2 22 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 188 (Polychromatic418967fa.accept_18_3_9_8_1_2977 21 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 188 (Polychromatic418967fa.accept_15_5_12_8_1_3168 20 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 188 (accept_3_2 19 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 117 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 188 (accept_3_2 16 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 188 (Polychromatic418967fa.accept_19_14_3_17_1_6558 14 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 188 (accept_3_2 13 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 188 (Polychromatic418967fa.accept_17_12_15_1_1_5798 12 117
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 188 (accept_3_2 10 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 117 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 188 (accept_3_2 7 117 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 188 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 188 (accept_3_2 4 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 188 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 117 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 188 (Polychromatic418967fa.accept_19_2_3_17_1_5146 2 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 188 (accept_3_2 1 117 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 116 188 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 116 188 4 18 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 188 (Polychromatic418967fa.accept_11_5_6_1_1_988 71 116 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 188 2 35 58 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 188
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 69 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 188 4 17 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 188 (accept_3_2 67 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 188 2 33 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 116 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 188 4 16 29 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 188
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 116 188 2 31 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 116 188 (accept_3_2 61 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 188 4 15 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 116 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 188 2 29 58 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 188
  (Polychromatic418967fa.accept_13_5_12_6_1_508 57 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 188 4 14 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 188 (accept_3_2 55 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 188 2 27 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 188 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 116 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 188 4 13 29 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 188 2 25 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 188 (accept_3_2 49 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 188 4 12 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 116 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 188 2 23 58 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 188 4 11 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 188 (accept_3_2 43 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 188 2 21 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 188 (Polychromatic418967fa.accept_13_2_12_6_1_2394 41 116 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 188 4 10 29 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 188
  (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 188 2 19 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 188 (accept_3_2 37 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 188 4 9 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 188 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 116 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 188 2 17 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 33
  116 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 116 188 4 8 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 116 188 (accept_3_2 31
  116 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 116 188 2 15 58 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 188
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 116 188 4 7 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 116 188 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 116 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 188 2 13 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 188 (accept_3_2 25 116 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 188 4 6 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 116 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 188 2 11 58 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 188
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 188 4 5 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 188 (accept_3_2 19 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  116 188 2 9 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 116 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 116 188 4 4 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 116 188 (Polychromatic418967fa.accept_13_2_12_6_1_2394 15 116 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 188 2 7 58 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 188 (accept_3_2 13 116 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 188 4 3 29 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 188
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 116 188 2 5 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 116 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 116 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 188 4 2 29 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 188 (accept_3_2 7 116 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 188 2 3 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 116 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 188 4 1 29 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 188 2 1 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 188 (accept_3_2 1 116 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 115 188 (Eq.refl
  Bool.true) (allA_of_3_0 74 115 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 114 188 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 114 188 2 37 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 114 188 (accept_3_2 73 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 188 2 36 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 114 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 188 2 35 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 114 188
  (Polychromatic418967fa.accept_10_9_4_8_1_741 69 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 114 188 2 34 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 114 188 (accept_3_2 67 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 188 2 33 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 114 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 188 2 32 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 188
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 114 188 2 31 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 188 (accept_3_2 61 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 188 2 30 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 114 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 188 2 29 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 188 2 28 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 188 (accept_3_2 55 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 188 2 27 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 114 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 188 2 26 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 188 2 25 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 188 (accept_3_2 49 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 188 2 24 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 114 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 188 2 23 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 188 2 22 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 188 (accept_3_2 43 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 188 2 21 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 114 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 188 2 20 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 188 2 19 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 188 (accept_3_2 37 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 188 2 18 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 188 (Polychromatic418967fa.accept_13_9_10_6_1_1028 35 114 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 188 2 17 57 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 188 2 16 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 188 (accept_3_2 31 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 188 2 15 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 114 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 188 2 14 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 188 2 13 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 188 (accept_3_2 25 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 188 2 12 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 114 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 188 2 11 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 188
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 188 2 10 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 188 (accept_3_2 19 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 188 2 9 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 114 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 188 2 8 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  114 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 188 2 7 57 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 188 (accept_3_2 13
  114 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 188 2 6 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 114 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 188 2 5 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 114 188 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 114 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 188 2 4 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 188 (accept_3_2 7 114 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 114 188 2 3 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 114 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 114 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 188 2 2 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 114 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 3
  114 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 188 2 1 57 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 188 (accept_3_2 1
  114 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 113 188 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 74
  113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 113 188 (accept_3_2 73
  113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 113 188
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 113 188 (Polychromatic418967fa.accept_10_1_3_8_1_136 71 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 188 (accept_3_2 70 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 188 (Polychromatic418967fa.accept_7_5_1_6_1_163
  68 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 188 (accept_3_2 67
  113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 113 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 66 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 113 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 188 (accept_3_2 64 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 188 (Polychromatic418967fa.accept_12_2_5_8_1_159
  62 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 188 (accept_3_2 61
  113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 188
  (Polychromatic418967fa.accept_9_6_5_8_1_598 60 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 113 188 (Polychromatic418967fa.accept_13_7_9_6_1_148 59 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 188 (accept_3_2 58 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 56
  113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 188 (accept_3_2 55
  113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 113 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 188 (accept_3_2 52 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 188 (Polychromatic418967fa.accept_12_2_5_8_1_159
  50 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 188 (accept_3_2 49
  113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 113 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 188 (accept_3_2 46 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 188 (Polychromatic418967fa.accept_7_2_1_6_1_173
  44 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 188 (accept_3_2 43
  113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 188
  (Polychromatic418967fa.accept_9_6_5_8_1_598 42 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 113 188 (Polychromatic418967fa.accept_10_1_3_8_1_136 41 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 188 (accept_3_2 40 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 38
  113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 188 (accept_3_2 37
  113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 188
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 113 188 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 188 (accept_3_2 34 113 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 188
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 32 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 188 (accept_3_2 31 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 188 (accept_3_2 28 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 113 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 188 (accept_3_2 25 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 188 (accept_3_2 22 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 188 (accept_3_2 19 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 188 (Polychromatic418967fa.accept_16_2_1_12_1_3798 18 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 188 (Polychromatic418967fa.accept_13_4_9_6_1_2376 17 113 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 188 (accept_3_2 16 113 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 188 (accept_3_2 13 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 188 (accept_3_2 10 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 188
  (Polychromatic418967fa.accept_16_8_1_12_1_984 8 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 188 (accept_3_2 7 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 188 (accept_3_2 4 113 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 188
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 188 (accept_3_2 1 113 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 112 188 (Eq.refl
  Bool.true) (allA_of_3_0 77 112 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 111 188 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 111 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 111 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 188 (accept_3_2 76 111 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 188 (Polychromatic418967fa.accept_9_2_3_8_1_318
  74 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 188 (accept_3_2 73
  111 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 188
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 72 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 111 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 188 (accept_3_2 70 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 111 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 111 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 111 188 (accept_3_2 67 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 111 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 111 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 188 (accept_3_2 64 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 111 188 (Polychromatic418967fa.accept_10_3_1_8_1_132 63 111 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 188
  (Polychromatic418967fa.accept_15_2_6_8_1_754 62 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 188 (accept_3_2 61 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 111 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 111 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 188 (accept_3_2 58 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 188 (Polychromatic418967fa.accept_20_17_11_8_1_4894 57 111 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 188 (accept_3_2 55 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 111 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 111 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 188 (accept_3_2 52 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 111 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 188 (accept_3_2 49 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 111 188 (Polychromatic418967fa.accept_13_9_7_6_1_1673 48 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 111 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 188 (accept_3_2 46 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 188 (Polychromatic418967fa.accept_16_13_15_12_1_1748 45 111 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 188
  (Polychromatic418967fa.accept_15_14_6_8_1_1410 44 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 188 (accept_3_2 43 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 111 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 111 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 188 (accept_3_2 40 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 188 (Polychromatic418967fa.accept_10_9_1_8_1_755 39 111 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 188 (accept_3_2 37 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 111 188 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 188 (accept_3_2 34 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 111 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 188 (accept_3_2 31 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 111 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 111 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 188 (accept_3_2 28 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 111 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 188
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 111 188 (accept_3_2 25 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 111 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 111 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 188 (accept_3_2 22 111 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 188
  (Polychromatic418967fa.accept_14_7_13_6_1_1177 21 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 111 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 188 (accept_3_2 19 111 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 111 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 188 (accept_3_2 16 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 188 (accept_3_2 13 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 188 (Polychromatic418967fa.accept_13_12_7_6_1_1015 12 111 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 188 (accept_3_2 10 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 188 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 188 (Polychromatic418967fa.accept_16_8_15_12_1_1747 8 111 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 188 (accept_3_2 7 111 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 111 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 188 (accept_3_2 4 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 111 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 188 (accept_3_2 1 111 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 79 110 188 (Eq.refl Bool.true) (allA_succ_of_gcd 78 110 188 2 39 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 110 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 110 188 2 38 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 110 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 110 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 110 188 2 37 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 110 188 (accept_3_2 73 110 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 110 188 2 36 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 110 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 71
  110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 188 2 35 55 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 188
  (Polychromatic418967fa.accept_9_6_2_8_1_592 69 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 110 188 2 34 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 110 188 (accept_3_2 67 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 188 2 33 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 110 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 110 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 188 2 32 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 188
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 188 2 31 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 188 (accept_3_2 61 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 188 2 30 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 110 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 188 2 29 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 188 2 28 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 188 (accept_3_2 55 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 188 2 27 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 110 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 188 2 26 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 188
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 188 2 25 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 188 (accept_3_2 49 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 188 2 24 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 110 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 188 2 23 55 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 188
  (Polychromatic418967fa.accept_17_11_8_1_1_3362 45 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 188 2 22 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 110 188 (accept_3_2 43 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 188 2 21 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 110 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 188 2 20 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 188 2 19 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 188 (accept_3_2 37 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 188 2 18 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 110 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 188 2 17 55 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 188
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 188 2 16 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 188 (accept_3_2 31 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 188 2 15 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 110 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 188 2 14 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 188
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 110 188 2 13 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 110 188 (accept_3_2 25 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 188 2 12 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 110 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 188 2 11 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 188
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 188 2 10 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 188 (accept_3_2 19 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 188 2 9 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 110 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 188 2 8 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 188 2 7 55 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 188 (accept_3_2 13
  110 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 188 2 6 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 188 2 5 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 188 (Polychromatic418967fa.accept_17_9_8_1_1_7036 9 110 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 188 2 4 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 188 (accept_3_2 7 110 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 110 188 2 3 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 110 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 110 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 188 2 2 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  110 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 188 2 1 55 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 188 (accept_3_2 1
  110 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 109 188 (Eq.refl
  Bool.true) (allA_of_3_0 80 109 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 108 188 (Eq.refl Bool.true)
  (allA_succ_of_gcd 80 108 188 4 20 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 108 188 (accept_3_2 79 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 188 2 39 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 188 (Polychromatic418967fa.accept_24_5_12_20_1_3817 77 108 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 188 4 19 27 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 108 188
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 75 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 108 188 2 37 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 108 188 (accept_3_2 73 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 188 4 18 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 188 (Polychromatic418967fa.accept_15_11_3_8_1_750 71 108 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 188 2 35 54 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 108 188
  (Polychromatic418967fa.accept_15_9_3_8_1_3155 69 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 108 188 4 17 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 108 188 (accept_3_2 67 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 188 2 33 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 108 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 188 4 16 27 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 108 188
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 63 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 108 188 2 31 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 108 188 (accept_3_2 61 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 188 4 15 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 188 (Polychromatic418967fa.accept_13_7_4_6_1_3221 59 108 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 188 2 29 54 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 108 188
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 57 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 108 188 4 14 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 188 (accept_3_2 55 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 188 2 27 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 108 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 188 4 13 27 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 108 188 2 25 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 188 (accept_3_2 49 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 188 4 12 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 188 (Polychromatic418967fa.accept_19_9_13_17_1_9506 47 108 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 188 2 23 54 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 188
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 108 188 4 11 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 108 188 (accept_3_2 43 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 188 2 21 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 188 (Polychromatic418967fa.accept_13_2_4_6_1_2356 41 108 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 188 4 10 27 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 188 2 19 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 188 (accept_3_2 37 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 188 4 9 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 188 (Polychromatic418967fa.accept_13_9_4_6_1_1005 35 108 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 188 2 17 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 188 (Polychromatic418967fa.accept_13_7_4_6_1_3221
  33 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 188 4 8 27 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 188
  (accept_3_2 31 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 188 2 15 54 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 188
  (Polychromatic418967fa.accept_17_12_6_1_1_4517 29 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 188 4 7 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 108 188 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 108 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 188 2 13 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 188 (accept_3_2 25 108 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 188 4 6 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 108 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 188 2 11 54 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 188
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 188 4 5 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 108 188 (accept_3_2 19 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  108 188 2 9 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 108 188 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 108 188 4 4 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 108 188 (Polychromatic418967fa.accept_13_2_4_6_1_2356 15 108 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 188 2 7 54 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 188 (accept_3_2 13 108 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 188 4 3 27 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 188 2 5 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 108 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 108 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 188 4 2 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 188 (accept_3_2 7 108 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 108 188 2 3 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 108 188 (Polychromatic418967fa.accept_13_5_4_6_1_2371 5 108 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 188 4 1 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 188 (Polychromatic418967fa.accept_14_3_10_6_1_1136
  3 108 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 188 2 1 54 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 188 (accept_3_2 1
  108 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 107 188 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 107 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 80
  107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 107 188 (accept_3_2 79
  107 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 107 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 107 188 (Polychromatic418967fa.accept_18_5_17_8_1_2984 77 107 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 188 (accept_3_2 76 107 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 107 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 188 (Polychromatic418967fa.accept_7_4_2_6_1_337
  74 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 188 (accept_3_2 73
  107 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 188
  (Polychromatic418967fa.accept_16_8_11_12_1_962 72 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 107 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 107 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 188 (accept_3_2 70 107 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 107 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 188
  (Polychromatic418967fa.accept_16_4_11_12_1_1775 68 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 107 188 (accept_3_2 67 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 107 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 107 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 188 (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 107
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 188 (accept_3_2 64 107
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 188
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 107 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 107 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 188 (accept_3_2 61 107 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 107 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 59
  107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 188 (accept_3_2 58
  107 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 188
  (Polychromatic418967fa.accept_6_3_5_2_1_12 57 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 107 188 (Polychromatic418967fa.accept_16_8_11_12_1_962 56 107 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 188 (accept_3_2 55 107 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 107 188 (Polychromatic418967fa.accept_15_9_2_8_1_1379 54 107 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 188 (accept_3_2 52 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 188 (accept_3_2 49 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 188 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 107 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 188
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 188 (accept_3_2 46 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 188 (Polychromatic418967fa.accept_13_5_3_6_1_3278 44 107 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 188 (accept_3_2 43 107 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 188 (Polychromatic418967fa.accept_16_10_11_12_1_4835 42
  107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 188
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 41 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 188 (accept_3_2 40 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 188 (accept_3_2 37 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 107 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 188
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 188 (accept_3_2 34 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 188 (accept_3_2 31 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 188 (Polychromatic418967fa.accept_20_10_7_8_1_4923 30 107 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 188 (accept_3_2 28 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 188 (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 107 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 188 (accept_3_2 25 107 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 107 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 188
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 188 (accept_3_2 22 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 188 (Polychromatic418967fa.accept_16_4_11_12_1_1775 20 107 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 188 (accept_3_2 19 107 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 107 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 188 (accept_3_2 16 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 107 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 188 (accept_3_2 13 107 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 188 (Polychromatic418967fa.accept_23_12_15_4_1_5645 12 107
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 188 (accept_3_2 10 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 188 (accept_3_2 7 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 188 (Polychromatic418967fa.accept_15_6_2_8_1_2223 6 107 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 188
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 188 (accept_3_2 4 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 188 (accept_3_2 1 107 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 106 188 (Eq.refl
  Bool.true) (allA_of_3_0 83 106 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 105 188 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 105 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 188 (accept_3_2 82 105 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 105 188 (Polychromatic418967fa.accept_13_3_1_6_1_509 81 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 188
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 80 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 105 188 (accept_3_2 79 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 105 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 188 (accept_3_2 76 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 105 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 105 188 (accept_3_2 73 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 105 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 105 188 (accept_3_2 70 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 105 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 105 188 (accept_3_2 67 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 105 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 188 (accept_3_2 64 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 105 188 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 188
  (Polychromatic418967fa.accept_10_2_5_8_1_139 62 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 188 (accept_3_2 61 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 105 188 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 188 (accept_3_2 58 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 105 188 (accept_3_2 55 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 105 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 188 (accept_3_2 52 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 188 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 105 188 (accept_3_2 49 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 105 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 188 (accept_3_2 46 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 188
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 44 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 188 (accept_3_2 43 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 105 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 188 (accept_3_2 40 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 188 (accept_3_2 37 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 188 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 188 (accept_3_2 34 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 188 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 188 (accept_3_2 31 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 188 (accept_3_2 28 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 188 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 188
  (Polychromatic418967fa.accept_17_9_3_1_1_2275 26 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 188 (accept_3_2 25 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 188 (Polychromatic418967fa.accept_16_8_9_12_1_1737 24 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 188 (accept_3_2 22 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 188 (accept_3_2 19 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 188 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 188 (accept_3_2 16 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 188 (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 188 (accept_3_2 13 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 188 (accept_3_2 10 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 188 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 188
  (Polychromatic418967fa.accept_13_8_1_6_1_997 8 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 188 (accept_3_2 7 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 188 (accept_3_2 4 105 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 105 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 188 (accept_3_2 1 105 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 104 188
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 104 188 4 21 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 104 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 104 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 188 2 41 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 188
  (Polychromatic418967fa.accept_15_6_14_8_1_245 81 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 188 4 20 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 188 (accept_3_2 79 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 188 2 39 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 188 (Polychromatic418967fa.accept_16_13_8_12_1_2723 77 104 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 188 4 19 26 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 75 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 188 2 37 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 188 (accept_3_2 73 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 188 4 18 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 104 188 (Polychromatic418967fa.accept_16_7_8_12_1_4902 71 104 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 188 2 35 52 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 188
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 188 4 17 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 188 (accept_3_2 67 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 188 2 33 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 104 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 188 4 16 26 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 188
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 63 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 104 188 2 31 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 104 188 (accept_3_2 61 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 188 4 15 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 188 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 104 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 188 2 29 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 188 4 14 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 188 (accept_3_2 55 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 188 2 27 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 188 (Polychromatic418967fa.accept_16_5_8_12_1_1766 53 104 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 188 4 13 26 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 188
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 188 2 25 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 188 (accept_3_2 49 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 188 4 12 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 104 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 188 2 23 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 188
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 45 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 104 188 4 11 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 104 188 (accept_3_2 43 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 188 2 21 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 188 (Polychromatic418967fa.accept_16_9_8_12_1_979 41 104 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 188 4 10 26 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 188 2 19 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 188 (accept_3_2 37 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 188 4 9 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 104 188 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 104 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 188 2 17 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 33
  104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 188 4 8 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 188 (accept_3_2 31
  104 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 188 2 15 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 104 188 4 7 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 104 188 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 104 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 188 2 13 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 188 (accept_3_2 25 104 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 104 188 4 6 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 104 188 (Polychromatic418967fa.accept_16_7_8_12_1_4902
  23 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 188 2 11 52 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 188 4 5 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 104 188 (accept_3_2 19 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  104 188 2 9 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 104 188 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 104 188 4 4 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 104 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 104 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 188 2 7 52 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 188 (accept_3_2 13 104 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 188 4 3 26 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 188 2 5 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 188 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 104 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 188 4 2 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 188 (accept_3_2 7 104 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 188 2 3 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 188 (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 104 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 188 4 1 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 3
  104 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 188 2 1 52 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 188 (accept_3_2 1
  104 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 103 188
  (Eq.refl Bool.true) (allA_of_3_0 86 103 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 102 188 (Eq.refl
  Bool.true) (allA_succ_of_gcd 86 102 188 2 43 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 102 188 (accept_3_2 85 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 188 2 42 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 102 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 188 2 41 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 102 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 102 188 2 40 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 102 188 (accept_3_2 79 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 188 2 39 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 102 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 188 2 38 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 102 188
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 102 188 2 37 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 102 188 (accept_3_2 73 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 188 2 36 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 188 (Polychromatic418967fa.accept_15_11_12_8_1_739 71 102 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 188 2 35 51 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 188
  (Polychromatic418967fa.accept_9_6_3_8_1_595 69 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 188 2 34 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 102 188 (accept_3_2 67 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 188 2 33 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 102 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 188 2 32 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 102 188 2 31 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 188 (accept_3_2 61 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 188 2 30 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 102 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 188 2 29 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 188
  (Polychromatic418967fa.accept_11_2_3_1_1_244 57 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 188 2 28 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 188 (accept_3_2 55 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 188 2 27 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 188 (Polychromatic418967fa.accept_19_15_7_17_1_5168 53 102 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 188 2 26 51 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 188 2 25 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 188 (accept_3_2 49 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 188 2 24 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 102 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 188 2 23 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 188 2 22 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 188 (accept_3_2 43 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 188 2 21 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 102 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 188 2 20 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 188 2 19 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 188 (accept_3_2 37 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 188 2 18 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 102 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 188 2 17 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 188
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 188 2 16 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 188 (accept_3_2 31 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 188 2 15 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 102 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 188 2 14 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 188 2 13 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 188 (accept_3_2 25 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 188 2 12 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 102 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 188 2 11 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 188 2 10 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 188 (accept_3_2 19 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 188 2 9 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 102 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 188 2 8 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 188 2 7 51 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 188 (accept_3_2 13
  102 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 188 2 6 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 188 2 5 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 102 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 102 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 188 2 4 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 188 (accept_3_2 7 102 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 102 188 2 3 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 102 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 102 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 188 2 2 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  102 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 188 2 1 51 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 188 (accept_3_2 1
  102 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 101 188
  (Eq.refl Bool.true) (allA_succ_of_accept 87 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 86 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 188 (accept_3_2 85 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 188 (Polychromatic418967fa.accept_10_3_1_8_1_132 83 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 188 (accept_3_2 82 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 101 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 188
  (Polychromatic418967fa.accept_11_3_2_1_1_994 80 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 188 (accept_3_2 79 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 188 (accept_3_2 76 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 74 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 101 188 (accept_3_2 73 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 101 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 188 (Polychromatic418967fa.accept_16_7_5_12_1_4824 71 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 188 (accept_3_2 70 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 101 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 188 (accept_3_2 67 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 188 (accept_3_2 64 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 62 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 188 (accept_3_2 61 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 188 (accept_3_2 58 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 188
  (Polychromatic418967fa.accept_13_4_10_6_1_989 56 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 188 (accept_3_2 55 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 188 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 188 (accept_3_2 52 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 188 (accept_3_2 49 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 188 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 188 (accept_3_2 46 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 188 (accept_3_2 43 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 188 (accept_3_2 40 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 188 (accept_3_2 37 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 188 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 188 (Polychromatic418967fa.accept_13_9_10_6_1_1028 35 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 188 (accept_3_2 34 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 188 (accept_3_2 31 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 188 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 188 (accept_3_2 28 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 188 (accept_3_2 25 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 188 (accept_3_2 22 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 188
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 20 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 188 (accept_3_2 19 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 188 (accept_3_2 16 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 188 (accept_3_2 13 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 188 (accept_3_2 10 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 188
  (Polychromatic418967fa.accept_16_8_5_12_1_3812 8 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 188 (accept_3_2 7 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 188 (accept_3_2 4 101 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 188 (accept_3_2 1 101 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 100 188
  (Eq.refl Bool.true) (allA_of_3_0 89 100 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 99 188 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 188 (accept_3_2 88 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 188
  (Polychromatic418967fa.accept_7_2_1_6_1_173 86 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 188 (accept_3_2 85 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 188 (accept_3_2 82 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 188 (Polychromatic418967fa.accept_10_1_9_8_1_123 81 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 188
  (Polychromatic418967fa.accept_13_2_8_6_1_2390 80 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 188 (accept_3_2 79 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 188 (accept_3_2 76 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 188
  (Polychromatic418967fa.accept_10_4_9_8_1_125 74 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 188 (accept_3_2 73 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 188 (accept_3_2 70 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 188 (Polychromatic418967fa.accept_20_9_19_8_1_1151 69 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 188 (accept_3_2 67 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 188 (accept_3_2 64 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 188
  (Polychromatic418967fa.accept_15_2_9_8_1_736 62 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 188 (accept_3_2 61 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 188 (Polychromatic418967fa.accept_18_6_9_8_1_6812 60 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 188 (accept_3_2 58 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 188 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 188
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 56 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 188 (accept_3_2 55 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 188 (accept_3_2 52 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 188
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 50 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 188 (accept_3_2 49 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 188 (Polychromatic418967fa.accept_15_3_9_8_1_3164 48 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 188 (accept_3_2 46 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 188 (Polychromatic418967fa.accept_22_1_11_12_1_7713 45 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 188
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 188 (accept_3_2 43 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 188 (accept_3_2 40 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 188
  (Polychromatic418967fa.accept_17_4_14_1_1_1363 38 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 188 (accept_3_2 37 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 188 (Polychromatic418967fa.accept_16_4_3_12_1_4892 36 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 188 (accept_3_2 34 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 188
  (Polychromatic418967fa.accept_15_2_9_8_1_736 32 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 188 (accept_3_2 31 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 188 (accept_3_2 28 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 188 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 188 (accept_3_2 25 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 188 (accept_3_2 22 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 188 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 188
  (Polychromatic418967fa.accept_16_4_3_12_1_4892 20 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 188 (accept_3_2 19 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 188 (accept_3_2 16 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 188
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 188 (accept_3_2 13 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 188 (accept_3_2 10 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 99 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 188
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 188 (accept_3_2 7 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  188 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 188 (accept_3_2 4 99 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 188 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 99 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  99 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 188 (accept_3_2 1 99 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 98 188
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 98 188 2 45 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 98 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 98 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 98 188 2 44 49 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 98 188
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 87 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 98 188 2 43 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 85 98 188 (accept_3_2 85 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98
  188 2 42 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83
  98 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 98 188 2 41 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 98 188 (Polychromatic418967fa.accept_16_1_2_12_1_1757 81 98 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 98 188 2 40 49 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 98 188 (accept_3_2 79 98 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 98 188 2 39 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 98 188
  (Polychromatic418967fa.accept_12_5_2_8_1_172 77 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 98 188 2 38 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 98 188 (Polychromatic418967fa.accept_11_9_10_1_1_581 75 98 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 98 188 2 37 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 98 188 (accept_3_2 73 98 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 98 188 2 36 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 98 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 98 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 188 2 35 49 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 188
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 69 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 98 188 2 34 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 98 188 (accept_3_2 67 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 98
  188 2 33 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  98 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 98 188 2 32 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 98 188 (Polychromatic418967fa.accept_16_15_2_12_1_1799 63 98 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 98 188 2 31 49 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 98 188 (accept_3_2 61 98 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 98 188 2 30 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 98 188
  (Polychromatic418967fa.accept_12_11_2_8_1_511 59 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 98 188 2 29 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 98 188 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 98 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 188 2 28 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 188 (accept_3_2 55 98 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 98 188 2 27 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 98 188 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 98 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 188 2 26 49 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 188
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 51 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 188 2 25 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 98 188 (accept_3_2 49 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 98
  188 2 24 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  98 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 98 188 2 23 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 98 188 (Polychromatic418967fa.accept_27_18_17_26_1_10801 45 98 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 98 188 2 22 49 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 98 188 (accept_3_2 43
  98 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98 188 2 21 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 98 188
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 98 188 2 20 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 98 188 (Polychromatic418967fa.accept_16_7_2_12_1_1754 39 98 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 98 188 2 19 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 98 188 (accept_3_2 37 98 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98 188 2 18 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 98 188 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 98 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 188 2 17 49 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 188
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 33 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 188 2 16 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 98 188 (accept_3_2 31 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98
  188 2 15 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  98 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 98 188 2 14 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 98 188 (Polychromatic418967fa.accept_13_1_7_6_1_142 27 98 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 98 188 2 13 49 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 98 188 (accept_3_2 25 98 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98 188 2 12 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 98 188
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 98 188 2 11 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 98 188 (Polychromatic418967fa.accept_19_2_3_17_1_5146 21 98 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 188 2 10 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 188 (accept_3_2 19 98 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 188 2 9 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 98 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 98 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 188 2 8 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 188
  (Polychromatic418967fa.accept_16_15_2_12_1_1799 15 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 188 2 7 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 188 (accept_3_2 13 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  188 2 6 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 188 2 5 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 188 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 98 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 188 2 4 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 188 (accept_3_2 7 98 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 188 2 3 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 98 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 188 2 2 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 188
  (Polychromatic418967fa.accept_20_3_18_8_1_4859 3 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 188 2 1 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 188 (accept_3_2 1 98 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 97 188
  (Eq.refl Bool.true) (allA_of_3_0 92 97 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 96 188 (Eq.refl
  Bool.true) (allA_succ_of_gcd 92 96 188 4 23 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 96 188 (accept_3_2 91 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 96 188 2 45 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 96 188 (Polychromatic418967fa.accept_13_11_5_6_1_519 89 96 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 188 4 22 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 188 (Polychromatic418967fa.accept_21_3_12_20_1_1891
  87 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 96 188 2 43 48 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 96 188 (accept_3_2 85
  96 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 188 4 21 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 96 188 2 41 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 81 96 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 96 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 188 4 20 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 188 (accept_3_2 79 96 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 188 2 39 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 96 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 96 188 4 19 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 96 188
  (Polychromatic418967fa.accept_9_3_6_8_1_308 75 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 96 188 2 37 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 96 188 (accept_3_2 73 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96
  188 4 18 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  96 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 96 188 2 35 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 96 188 (Polychromatic418967fa.accept_13_4_5_6_1_3201 69 96 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 96 188 4 17 24 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 96 188 (accept_3_2 67 96 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 188 2 33 48 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 96 188 4 16 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 96 188 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 96 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 188 2 31 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 188 (accept_3_2 61 96 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 188 4 15 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 96 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 188 2 29 48 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 96 188 4 14 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 96 188 (accept_3_2 55 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96
  188 2 27 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  96 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 96 188 4 13 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 96 188 (Polychromatic418967fa.accept_13_12_5_6_1_1050 51 96 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 188 2 25 48 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 188 (accept_3_2 49 96 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 188 4 12 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 96 188 2 23 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 96 188 (Polychromatic418967fa.accept_18_9_6_8_1_2989 45 96 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 188 4 11 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 188 (accept_3_2 43 96 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 188 2 21 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 96 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 188 4 10 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 96 188 2 19 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 96 188 (accept_3_2 37 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96
  188 4 9 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  96 188 (Polychromatic418967fa.accept_19_16_1_17_1_8065 35 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 96 188 2 17 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 96 188 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 96 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 96 188 4 8 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 188 (accept_3_2 31 96 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 188 2 15 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 29
  96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 188 4 7 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 188
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 96 188 2 13 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 96 188 (accept_3_2 25 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96
  188 4 6 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  96 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 96 188 2 11 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 96 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 188 4 5 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 188 (accept_3_2 19 96 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 188 2 9 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 188 (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 96 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 188 4 4 24 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 96 188 2 7 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 188 (accept_3_2 13 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96
  188 4 3 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  96 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 96 188 2 5 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 96 188 (Polychromatic418967fa.accept_18_9_6_8_1_2989 9 96 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 188 4 2 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 188 (accept_3_2 7 96 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 188 2 3 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 96 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 188 4 1 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96 188
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 188 2 1 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 188 (accept_3_2 1 96 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 95 188
  (Eq.refl Bool.true) (allA_succ_of_accept 93 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 95 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 92 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 95 188 (accept_3_2 91 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  95 188 (Polychromatic418967fa.accept_20_10_15_8_1_4818 90 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 95 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 89 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 95 188 (accept_3_2 88 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 95 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 86 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 95 188 (accept_3_2 85 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  95 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 95 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 83 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 95 188 (accept_3_2 82 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 95 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 80 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 95 188 (accept_3_2 79 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  95 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 95 188 (Polychromatic418967fa.accept_10_7_5_8_1_1167 77 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 95 188 (accept_3_2 76 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 95 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 95 188 (accept_3_2 73 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  95 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 95 188 (Polychromatic418967fa.accept_15_11_5_8_1_3157 71 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 95 188 (accept_3_2 70 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 95 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 188
  (Polychromatic418967fa.accept_7_5_4_6_1_167 68 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 95 188 (accept_3_2 67 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  95 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 95 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 95 188 (accept_3_2 64 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 95 188
  (Polychromatic418967fa.accept_10_2_5_8_1_139 62 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 95 188 (accept_3_2 61 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  95 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 95 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 188 (accept_3_2 58 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 95 188 (accept_3_2 55 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  95 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 95 188 (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 188 (accept_3_2 52 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 95 188
  (Polychromatic418967fa.accept_11_6_7_1_1_564 50 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 95 188 (accept_3_2 49 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  95 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 95 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 188 (accept_3_2 46 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 95 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 95 188 (accept_3_2 43 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  95 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 95 188 (Polychromatic418967fa.accept_13_2_4_6_1_2356 41 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 95 188 (accept_3_2 40 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 95 188 (accept_3_2 37 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  95 188 (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 95 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 188 (accept_3_2 34 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 188
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 188 (accept_3_2 31 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  95 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 95 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 188 (accept_3_2 28 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 188
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 95 188 (accept_3_2 25 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  95 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 188 (accept_3_2 22 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 95 188 (accept_3_2 19 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  95 188 (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 95 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 188 (accept_3_2 16 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 188
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 188 (accept_3_2 13 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 188 (accept_3_2 10 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 188
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 8 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 188 (accept_3_2 7 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  188 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 95 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 188 (accept_3_2 4 95 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  95 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 188 (accept_3_2 1 95 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 188
  (allA_of_3_0 94 94 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 188 (allA_succ_of_accept 92 93 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 92 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 188 (accept_3_2 91 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 188 (accept_3_2 88 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 86 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 188 (accept_3_2 85 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 188 (Polychromatic418967fa.accept_15_9_3_8_1_3155 84 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 188 (accept_3_2 82 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 188 (accept_3_2 79 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 188 (accept_3_2 76 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 188 (Polychromatic418967fa.accept_10_5_3_8_1_1165 75 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 74 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 188 (accept_3_2 73 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 188 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 188 (accept_3_2 70 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 188 (accept_3_2 67 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 188 (accept_3_2 64 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 188 (Polychromatic418967fa.accept_16_15_13_12_1_1787 63 93 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 188
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 62 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 188 (accept_3_2 61 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 188 (accept_3_2 58 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 188 (accept_3_2 55 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 188 (accept_3_2 52 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 188 (accept_3_2 49 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 188 (Polychromatic418967fa.accept_13_9_2_6_1_514 48 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 188 (accept_3_2 46 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 188
  (Polychromatic418967fa.accept_21_2_9_20_1_9260 44 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 188 (accept_3_2 43 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 188 (accept_3_2 40 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 188 (accept_3_2 37 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 188 (accept_3_2 34 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 188 (accept_3_2 31 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 188 (accept_3_2 28 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 188 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 188
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 188 (accept_3_2 25 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 188 (accept_3_2 22 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 188 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 188 (accept_3_2 19 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 188 (accept_3_2 16 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 188 (accept_3_2 13 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 188 (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 188 (accept_3_2 10 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 93 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 188 (accept_3_2 7 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  188 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 188 (accept_3_2 4 93 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 93 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  93 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 188 (accept_3_2 1 93 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 188
  (allA_succ_of_accept 91 92 188 (accept_3_2 91 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  188 2 45 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89
  92 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 188 4 22 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 92 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 188 2 43 46 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 188 (accept_3_2 85 92 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 188 4 21 23 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 188
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 83 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 188 2 41 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 81 92 188 (Polychromatic418967fa.accept_13_3_1_6_1_509 81 92 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 188 4 20 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 188 (accept_3_2 79 92 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 188 2 39 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 92 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 188 4 19 23 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 188 2 37 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 92 188 (accept_3_2 73 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 92
  188 4 18 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  92 188 (Polychromatic418967fa.accept_18_17_2_8_1_6800 71 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 92 188 2 35 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 92 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 92 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 188 4 17 23 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 188 (accept_3_2 67 92 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 188 2 33 46 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 188
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 188 4 16 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 188 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 92 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 188 2 31 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 188 (accept_3_2 61 92 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 188 4 15 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 92 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 188 2 29 46 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 188
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 188 4 14 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 92 188 (accept_3_2 55 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92
  188 2 27 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  92 188 (Polychromatic418967fa.accept_18_17_2_8_1_6800 53 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 92 188 4 13 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 92 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 188 2 25 46 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 188 (accept_3_2 49 92 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 188 4 12 23 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 188 2 23 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 92 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 92 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 188 4 11 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 188 (accept_3_2 43 92 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 188 2 21 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 92 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 188 4 10 23 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 188
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 188 2 19 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 92 188 (accept_3_2 37 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92
  188 4 9 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  92 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 92 188 2 17 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 92 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 92 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 188 4 8 23 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 188 (accept_3_2 31 92 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 188 2 15 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 188 (Polychromatic418967fa.accept_13_3_1_6_1_509 29
  92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 92 188 4 7 23 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 188
  (Polychromatic418967fa.accept_17_10_7_1_1_7024 27 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 92 188 2 13 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 92 188 (accept_3_2 25 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92
  188 4 6 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  92 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 92 188 2 11 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 92 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 92 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 188 4 5 23 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 188 (accept_3_2 19 92 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 188 2 9 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 92 188 (Polychromatic418967fa.accept_18_17_2_8_1_6800 17 92 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 188 4 4 23 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 188
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 92 188 2 7 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 92 188 (accept_3_2 13 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92
  188 4 3 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  92 188 (Polychromatic418967fa.accept_17_11_7_1_1_7023 11 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 92 188 2 5 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 92 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 92 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 188 4 2 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 188 (accept_3_2 7 92 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 188 2 3 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 92 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 92 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 188 4 1 23 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 188
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 92 188 2 1 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 92 188 (accept_3_2 1 92 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 188
  (allA_of_3_0 91 91 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 188 (allA_succ_of_accept 89 90 188
  (Polychromatic418967fa.accept_17_4_5_1_1_5776 89 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 90 188 2 44 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 87 90 188 (Polychromatic418967fa.accept_11_10_2_1_1_1036 87 90 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 188 2 43 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 188 (accept_3_2 85 90 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 188 2 42 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 188 (Polychromatic418967fa.accept_13_5_12_6_1_508 83 90 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 188 2 41 45 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 188 2 40 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 90 188 (accept_3_2 79 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90
  188 2 39 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77
  90 188 (Polychromatic418967fa.accept_16_13_10_12_1_1811 77 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 90 188 2 38 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 90 188 (Polychromatic418967fa.accept_12_3_6_8_1_969 75 90 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 90 188 2 37 45 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 188 (accept_3_2 73 90 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 188 2 36 45 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 188
  (Polychromatic418967fa.accept_22_5_2_12_1_10800 71 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 90 188 2 35 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 90 188 (Polychromatic418967fa.accept_11_3_2_1_1_994 69 90 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 188 2 34 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 188 (accept_3_2 67 90 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 188 2 33 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 188 (Polychromatic418967fa.accept_11_10_2_1_1_1036 65 90 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 188 2 32 45 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 188 2 31 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 90 188 (accept_3_2 61 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90
  188 2 30 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  90 188 (Polychromatic418967fa.accept_13_7_12_6_1_1039 59 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 90 188 2 29 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 90 188 (Polychromatic418967fa.accept_12_9_6_8_1_518 57 90 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 188 2 28 45 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 188 (accept_3_2 55 90 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 188 2 27 45 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 188
  (Polychromatic418967fa.accept_16_5_10_12_1_4904 53 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 90 188 2 26 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 90 188 (Polychromatic418967fa.accept_12_3_6_8_1_969 51 90 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 188 2 25 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 188 (accept_3_2 49 90 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 188 2 24 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 188 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 90 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 188 2 23 45 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 188 2 22 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 90 188 (accept_3_2 43 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90
  188 2 21 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  90 188 (Polychromatic418967fa.accept_13_2_12_6_1_2394 41 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 90 188 2 20 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 90 188 (Polychromatic418967fa.accept_12_3_6_8_1_969 39 90 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 188 2 19 45 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 188 (accept_3_2 37 90 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 188 2 18 45 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 188
  (Polychromatic418967fa.accept_16_3_10_12_1_4814 35 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 90 188 2 17 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 90 188 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 90 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 188 2 16 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 188 (accept_3_2 31 90 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 188 2 15 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 188 (Polychromatic418967fa.accept_16_13_10_12_1_1811 29 90
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 188 2 14 45 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 188 2 13 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 90 188 (accept_3_2 25 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90
  188 2 12 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  90 188 (Polychromatic418967fa.accept_13_10_12_6_1_991 23 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 90 188 2 11 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 90 188 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 90 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 188 2 10 45 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 188 (accept_3_2 19 90 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 188 2 9 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 188 (Polychromatic418967fa.accept_20_17_10_8_1_9374
  17 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 188 2 8 45 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 90 188 2 7 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 90 188 (accept_3_2 13 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90
  188 2 6 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  90 188 (Polychromatic418967fa.accept_16_11_10_12_1_4832 11 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 188 2 5 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 90 188 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 90 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 188 2 4 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 188 (accept_3_2 7 90 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 188 2 3 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 90 188 (Polychromatic418967fa.accept_13_5_12_6_1_508 5 90 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 188 2 2 45 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 188
  (Polychromatic418967fa.accept_11_3_2_1_1_994 3 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 188 2 1 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 188 (accept_3_2 1 90 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 188
  (allA_succ_of_accept 88 89 188 (accept_3_2 88 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 188 (Polychromatic418967fa.accept_12_2_5_8_1_159 86 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 188 (accept_3_2 85 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 188
  (Polychromatic418967fa.accept_13_5_11_6_1_505 83 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 188 (accept_3_2 82 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 188 (Polychromatic418967fa.accept_15_5_14_8_1_1376 80 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 188 (accept_3_2 79 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 89 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 188
  (Polychromatic418967fa.accept_8_5_1_4_1_628 77 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 188 (accept_3_2 76 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 188 (accept_3_2 73 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 188 (Polychromatic418967fa.accept_16_8_9_12_1_1737 72 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 188 (accept_3_2 70 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 188 (Polychromatic418967fa.accept_16_4_9_12_1_4829 68 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 188 (accept_3_2 67 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 188 (Polychromatic418967fa.accept_15_6_14_8_1_245 66 89 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 188
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 188 (accept_3_2 64 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 188 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 188 (accept_3_2 61 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 188
  (Polychromatic418967fa.accept_17_8_4_1_1_5730 59 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 188 (accept_3_2 58 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 188 (Polychromatic418967fa.accept_13_4_11_6_1_1033 56 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 188 (accept_3_2 55 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 89 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 188 (accept_3_2 52 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 188 (accept_3_2 49 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 188 (Polychromatic418967fa.accept_17_14_4_1_1_3341 48 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 188
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 188 (accept_3_2 46 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 188 (accept_3_2 43 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 188 (Polychromatic418967fa.accept_17_8_4_1_1_5730 42 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 188
  (Polychromatic418967fa.accept_10_1_9_8_1_123 41 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 188 (accept_3_2 40 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 188 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 188 (accept_3_2 37 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 188
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 188 (accept_3_2 34 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 188 (accept_3_2 31 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 188 (Polychromatic418967fa.accept_13_4_11_6_1_1033 30 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 188 (accept_3_2 28 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 188 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 188 (accept_3_2 25 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 188
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 188 (accept_3_2 22 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 188 (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 188 (accept_3_2 19 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 89 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 188
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 188 (accept_3_2 16 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 188 (accept_3_2 13 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 188 (Polychromatic418967fa.accept_24_12_17_20_1_10793 12 89 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 188 (accept_3_2 10 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 188 (accept_3_2 7 89 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 188 (Polychromatic418967fa.accept_15_6_14_8_1_245 6 89 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 188
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 188 (accept_3_2 4 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 188 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 89 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 188 (accept_3_2 1 89 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 188 (allA_of_3_0 88 88 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 188
  (allA_succ_of_accept 86 87 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 87 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 188 (accept_3_2 85 87 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 188 (accept_3_2 82 87
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 81 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 188 (Polychromatic418967fa.accept_13_2_9_6_1_501 80 87 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 188 (accept_3_2 79 87 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 188 (accept_3_2 76 87
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 188 (Polychromatic418967fa.accept_8_3_7_4_1_42
  75 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 74 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 188 (accept_3_2 73 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 188 (accept_3_2 70 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 188 (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 87 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 188 (accept_3_2 67 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 188 (accept_3_2 64 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 188 (Polychromatic418967fa.accept_15_3_12_8_1_738 63 87 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 188
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 62 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 188 (accept_3_2 61 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 188 (accept_3_2 58 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 87 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 188 (accept_3_2 55 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 188 (accept_3_2 52 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 87 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 188 (accept_3_2 49 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 188 (accept_3_2 46 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 188 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 87 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 188 (accept_3_2 43 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 188 (Polychromatic418967fa.accept_11_9_10_1_1_581 42 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 188 (accept_3_2 40 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 87 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 188 (accept_3_2 37 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 188 (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 188 (accept_3_2 34 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 188 (Polychromatic418967fa.accept_13_7_9_6_1_148 33 87 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 188 (accept_3_2 31 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 188 (accept_3_2 28 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 87 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 188
  (Polychromatic418967fa.accept_15_11_12_8_1_739 26 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 188 (accept_3_2 25 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 188 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 188 (accept_3_2 22 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 87 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 188 (accept_3_2 19 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 188 (accept_3_2 16 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 188 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 87 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 188 (accept_3_2 13 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 188 (accept_3_2 10 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 87 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 188
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 8 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 188 (accept_3_2 7 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  188 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 87 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 188 (accept_3_2 4 87 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 87
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 188 (accept_3_2 1 87 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 188
  (allA_succ_of_accept 85 86 188 (accept_3_2 85 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  188 2 42 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83
  86 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 188 2 41 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 86 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 188 2 40 43 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 188 (accept_3_2 79 86 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 188 2 39 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 188
  (Polychromatic418967fa.accept_12_5_2_8_1_172 77 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 188 2 38 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 86 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 86 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 188 2 37 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 188 (accept_3_2 73 86 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 188 2 36 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 86 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 188 2 35 43 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 188
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 188 2 34 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 86 188 (accept_3_2 67 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 86
  188 2 33 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  86 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 86 188 2 32 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 86 188 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 86 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 86 188 2 31 43 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 86 188 (accept_3_2 61 86 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 86 188 2 30 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 86 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 86 188 2 29 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 86 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 86 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 86 188 2 28 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 86 188 (accept_3_2 55 86 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 86 188 2 27 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 86 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 86 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 188 2 26 43 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 188
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 188 2 25 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 86 188 (accept_3_2 49 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86
  188 2 24 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  86 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 86 188 2 23 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 86 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 86 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 86 188 2 22 43 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 86 188 (accept_3_2 43 86 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86 188 2 21 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 86 188
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 86 188 2 20 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 86 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 86 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 188 2 19 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 188 (accept_3_2 37 86 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 188 2 18 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 86 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 188 2 17 43 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 188
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 188 2 16 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 86 188 (accept_3_2 31 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86
  188 2 15 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  86 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 86 188 2 14 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 86 188 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 86 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 188 2 13 43 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 188 (accept_3_2 25 86 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 188 2 12 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 188
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 86 188 2 11 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 86 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 86 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 188 2 10 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 188 (accept_3_2 19 86 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 188 2 9 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 86 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 86 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 188 2 8 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 188 2 7 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 188 (accept_3_2 13 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  188 2 6 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 188 2 5 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 188 (Polychromatic418967fa.accept_21_9_2_20_1_857 9 86 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 188 2 4 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 188 (accept_3_2 7 86 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 188 2 3 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 86 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 188 2 2 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 188 2 1 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 188 (accept_3_2 1 86 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 188
  (allA_of_3_0 85 85 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 188 (allA_succ_of_accept 83 84 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 188 2 41 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 81 84 188 (Polychromatic418967fa.accept_16_1_4_12_1_376 81 84 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 188 4 20 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 188 (accept_3_2 79 84 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 188 2 39 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 84 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 188 4 19 21 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 188
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 75 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 188 2 37 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 84 188 (accept_3_2 73 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84
  188 4 18 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  84 188 (Polychromatic418967fa.accept_16_7_4_12_1_1806 71 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 84 188 2 35 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 84 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 84 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 188 4 17 21 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 188 (accept_3_2 67 84 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 188 2 33 42 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 188 4 16 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 188 (Polychromatic418967fa.accept_15_3_9_8_1_3164 63 84 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 188 2 31 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 188 (accept_3_2 61 84 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 188 4 15 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 84 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 188 2 29 42 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 188
  (Polychromatic418967fa.accept_16_9_4_12_1_4896 57 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 188 4 14 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 188 (accept_3_2 55 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84
  188 2 27 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  84 188 (Polychromatic418967fa.accept_16_5_4_12_1_3800 53 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 84 188 4 13 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 84 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 84 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 188 2 25 42 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 188 (accept_3_2 49 84 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 188 4 12 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 188 2 23 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 84 188 (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 84 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 188 4 11 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 188 (accept_3_2 43 84 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 188 2 21 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 188 4 10 21 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 188
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 188 2 19 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 84 188 (accept_3_2 37 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84
  188 4 9 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  84 188 (Polychromatic418967fa.accept_16_3_4_12_1_3799 35 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 84 188 2 17 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 84 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 188 4 8 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 188 (accept_3_2 31 84 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 188 2 15 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 29
  84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 188 4 7 21 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 188
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 27 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 84 188 2 13 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 84 188 (accept_3_2 25 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84
  188 4 6 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  84 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 84 188 2 11 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 84 188 (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 84 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 84 188 4 5 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 188 (accept_3_2 19 84 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 188 2 9 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 188 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 84 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 188 4 4 21 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 188
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 84 188 2 7 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 84 188 (accept_3_2 13 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84
  188 4 3 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  84 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 84 188 2 5 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 84 188 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 84 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 188 4 2 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 188 (accept_3_2 7 84 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 188 2 3 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 84 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 188 4 1 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 188
  (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 84 188 2 1 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 188 (accept_3_2 1 84 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 188
  (allA_succ_of_accept 82 83 188 (accept_3_2 82 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 188 (Polychromatic418967fa.accept_17_12_15_1_1_5798 80 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 188 (accept_3_2 79 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 83 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 188 (accept_3_2 76 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 188 (accept_3_2 73 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 188 (Polychromatic418967fa.accept_16_8_3_12_1_1819 72 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 188
  (Polychromatic418967fa.accept_8_7_3_4_1_404 71 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 188 (accept_3_2 70 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 188 (accept_3_2 67 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 188
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 65 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 188 (accept_3_2 64 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 188 (Polychromatic418967fa.accept_11_7_6_1_1_2182 62 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 188 (accept_3_2 61 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 188 (accept_3_2 58 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 188 (accept_3_2 55 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 188 (Polychromatic418967fa.accept_14_12_13_6_1_1140 54 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 188
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 53 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 188 (accept_3_2 52 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 188 (accept_3_2 49 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 188
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 188 (accept_3_2 46 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 188 (Polychromatic418967fa.accept_25_19_8_13_1_10799 44 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 188 (accept_3_2 43 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 83 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 188 (accept_3_2 40 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 188 (Polychromatic418967fa.accept_11_5_6_1_1_988 38 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 188 (accept_3_2 37 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 188
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 188 (accept_3_2 34 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 188 (accept_3_2 31 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 188
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 188 (accept_3_2 28 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 188 (accept_3_2 25 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 188
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 188 (accept_3_2 22 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 188 (Polychromatic418967fa.accept_16_4_3_12_1_4892 20 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 188 (accept_3_2 19 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 188 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 83 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 188
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 188 (accept_3_2 16 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 188 (accept_3_2 13 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 188
  (Polychromatic418967fa.accept_10_1_3_8_1_136 11 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 188 (accept_3_2 10 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 188 (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 188 (accept_3_2 7 83 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 188 (accept_3_2 4 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 83 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 188 (accept_3_2 1 83 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 188 (allA_of_3_0 82 82 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 188
  (allA_succ_of_accept 80 81 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 188 (accept_3_2 79 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 188 (accept_3_2 76 81
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 188
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 188 (Polychromatic418967fa.accept_11_8_4_1_1_1000 74 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 188 (accept_3_2 73 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 71
  81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 188 (accept_3_2 70 81
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 188
  (Polychromatic418967fa.accept_8_5_1_4_1_628 69 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 188 (accept_3_2 67 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 65
  81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 188 (accept_3_2 64 81
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 188
  (Polychromatic418967fa.accept_10_3_1_8_1_132 63 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 188 (Polychromatic418967fa.accept_13_10_3_6_1_1003 62 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 188 (accept_3_2 61 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 188 (Polychromatic418967fa.accept_18_6_9_8_1_6812 60 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 59
  81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 188 (accept_3_2 58 81
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 188
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 57 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 188 (Polychromatic418967fa.accept_16_8_1_12_1_984 56 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 188 (accept_3_2 55 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 188 (accept_3_2 52 81
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 188 (Polychromatic418967fa.accept_16_2_1_12_1_3798 50 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 188 (accept_3_2 49 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 188 (Polychromatic418967fa.accept_13_9_3_6_1_1661 48 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 188 (accept_3_2 46 81
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 188 (accept_3_2 43 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41
  81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 188 (accept_3_2 40 81
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 188
  (Polychromatic418967fa.accept_10_9_1_8_1_755 39 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 188 (accept_3_2 37 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 188 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 81 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 188 (accept_3_2 34 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 188 (Polychromatic418967fa.accept_15_2_6_8_1_754 32 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 188 (accept_3_2 31 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 81 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 188 (accept_3_2 28 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 188 (Polychromatic418967fa.accept_13_1_3_6_1_158 27 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 188 (accept_3_2 25 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 188 (accept_3_2 22 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 188 (Polychromatic418967fa.accept_16_4_1_12_1_1792 20 81 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 188 (accept_3_2 19 81 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 81 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 188 (accept_3_2 16 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 188 (Polychromatic418967fa.accept_19_15_5_17_1_8036 15 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 188 (Polychromatic418967fa.accept_13_1_3_6_1_158 14 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 188 (accept_3_2 13 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 188 (accept_3_2 10 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 188 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 188 (accept_3_2 7 81 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 81 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 188 (accept_3_2 4 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  188 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 81 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 188 (accept_3_2 1 81 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 188 (allA_succ_of_accept 79 80 188 (accept_3_2 79 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 80 188 2 39 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 80 188 (Polychromatic418967fa.accept_13_12_2_6_1_2396 77 80 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 80 188 4 19 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 80 188 (Polychromatic418967fa.accept_13_10_2_6_1_1044
  75 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 80 188 2 37 40 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 188 (accept_3_2 73
  80 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 188 4 18 20 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 188
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 71 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 188 2 35 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 80 188 (Polychromatic418967fa.accept_13_4_2_6_1_1043 69 80 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 188 4 17 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 188 (accept_3_2 67 80 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 188 2 33 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 80 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 80 188 4 16 20 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 80 188
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 80 188 2 31 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 80 188 (accept_3_2 61 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80
  188 4 15 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  80 188 (Polychromatic418967fa.accept_14_3_10_6_1_1136 59 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 80 188 2 29 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 80 188 (Polychromatic418967fa.accept_11_2_3_1_1_244 57 80 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 80 188 4 14 20 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 80 188 (accept_3_2 55 80 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80 188 2 27 40 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 80 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 80 188 4 13 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 80 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 80 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 188 2 25 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 188 (accept_3_2 49 80 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 188 4 12 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 188 (Polychromatic418967fa.accept_13_8_2_6_1_2385 47 80 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 188 2 23 40 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 188
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 188 4 11 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 188 (accept_3_2 43 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  188 2 21 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  80 188 (Polychromatic418967fa.accept_15_11_5_8_1_3157 41 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 188 4 10 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 80 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 80 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 188 2 19 40 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 188 (accept_3_2 37 80 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 188 4 9 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 188 (Polychromatic418967fa.accept_11_2_3_1_1_244 35
  80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 188 2 17 40 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 188
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 33 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 188 4 8 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 188 (accept_3_2 31 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  188 2 15 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  80 188 (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 188 4 7 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 188 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 80 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 188 2 13 40 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 188 (accept_3_2 25 80 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 188 4 6 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 80 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 188 2 11 40 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 188
  (Polychromatic418967fa.accept_13_8_2_6_1_2385 21 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 188 4 5 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 188 (accept_3_2 19 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  188 2 9 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 188 (Polychromatic418967fa.accept_13_4_2_6_1_1043 17 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 188 4 4 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 188 (Polychromatic418967fa.accept_17_15_12_1_1_3365 15 80 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 188 2 7 40 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 188 (accept_3_2 13 80 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 188 4 3 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 80 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 188 2 5 40 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 188 4 2 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 188 (accept_3_2 7 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 188
  2 3 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  188 (Polychromatic418967fa.accept_28_5_24_20_1_10798 5 80 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 80 188 4 1 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 80 188 (Polychromatic418967fa.accept_14_3_10_6_1_1136 3 80 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 188 2 1 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 188 (accept_3_2 1 80 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 80 188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 79 188 (allA_of_3_0 79 79 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 188
  (allA_succ_of_accept 77 78 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 78 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 188 2 38 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 78 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 75
  78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 188 2 37 39 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 188 (accept_3_2 73
  78 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 188 2 36 39 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 188
  (Polychromatic418967fa.accept_15_11_3_8_1_750 71 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 188 2 35 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 78 188 (Polychromatic418967fa.accept_12_9_6_8_1_518 69 78 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 78 188 2 34 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 188 (accept_3_2 67 78 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 188 2 33 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 78 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 188 2 32 39 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 188 2 31 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 78 188 (accept_3_2 61 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78
  188 2 30 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  78 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 78 188 2 29 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 78 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 78 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 188 2 28 39 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 188 (accept_3_2 55 78 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 188 2 27 39 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 188
  (Polychromatic418967fa.accept_19_15_2_17_1_5163 53 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 188 2 26 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 78 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 78 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 188 2 25 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 188 (accept_3_2 49 78 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 188 2 24 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 78 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 188 2 23 39 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 188 2 22 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 78 188 (accept_3_2 43 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78
  188 2 21 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  78 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 78 188 2 20 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 78 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 78 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 188 2 19 39 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 188 (accept_3_2 37 78 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 188 2 18 39 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 188
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 35 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 188 2 17 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 78 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 78 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 188 2 16 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 188 (accept_3_2 31 78 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 188 2 15 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 78 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 188 2 14 39 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 188 2 13 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 188 (accept_3_2 25 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78
  188 2 12 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  78 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 78 188 2 11 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 78 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 78 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 188 2 10 39 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 188 (accept_3_2 19 78 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 188 2 9 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 188
  (Polychromatic418967fa.accept_25_17_3_13_1_10797 17 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 78 188 2 8 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 78 188 (Polychromatic418967fa.accept_12_3_6_8_1_969 15 78 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 188 2 7 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 188 (accept_3_2 13 78 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 188 2 6 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 78 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 78 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 188 2 5 39 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 188
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 188 2 4 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 188 (accept_3_2 7 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 188
  2 3 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78
  188 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 78 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 78 188 2 2 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 78 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 78 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 188 2 1 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 188 (accept_3_2 1 78 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  77 188 (allA_succ_of_accept 76 77 188 (accept_3_2 76 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 77 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 77 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 77 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 77 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 188 (accept_3_2 73 77 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 188 (Polychromatic418967fa.accept_13_7_12_6_1_1039
  72 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 188
  (Polychromatic418967fa.accept_14_1_7_6_1_3604 71 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 188 (accept_3_2 70 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 188 (Polychromatic418967fa.accept_16_4_13_12_1_1740 68 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 188 (accept_3_2 67 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 77 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 188
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 188 (accept_3_2 64 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 188 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 188 (accept_3_2 61 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 188
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 59 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 188 (accept_3_2 58 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 188 (accept_3_2 55 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 188 (Polychromatic418967fa.accept_13_2_12_6_1_2394 54 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 188
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 53 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 188 (accept_3_2 52 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 188 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 188 (accept_3_2 49 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 188 (accept_3_2 46 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 188 (Polychromatic418967fa.accept_13_5_12_6_1_508 44 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 188 (accept_3_2 43 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 188
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 188 (accept_3_2 40 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 188 (accept_3_2 37 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 188 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 188
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 188 (accept_3_2 34 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 188 (Polychromatic418967fa.accept_17_15_9_1_1_3363 32 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 188 (accept_3_2 31 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 77 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 188 (accept_3_2 28 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 188 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 188 (accept_3_2 25 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 188
  (Polychromatic418967fa.accept_13_10_12_6_1_991 23 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 188 (accept_3_2 22 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 188 (accept_3_2 19 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 188 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 188
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 188 (accept_3_2 16 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 188 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 188 (accept_3_2 13 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 188 (accept_3_2 10 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 188 (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 188 (accept_3_2 7 77 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 188
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 188 (accept_3_2 4 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 188 (accept_3_2 1 77 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 188 (allA_of_3_0 76 76 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 188 (allA_succ_of_accept 74 75
  188 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 188 (accept_3_2 73 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 188 (accept_3_2 70 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 75 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 188 (accept_3_2 67 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 188 (accept_3_2 64 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 75 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 188
  (Polychromatic418967fa.accept_10_2_5_8_1_139 62 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 188 (accept_3_2 61 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 188 (accept_3_2 58 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 75 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 188 (accept_3_2 55 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 188 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 188 (accept_3_2 52 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 75 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 188 (accept_3_2 49 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 188 (Polychromatic418967fa.accept_13_9_10_6_1_1028 48 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 188 (accept_3_2 46 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 188 (Polychromatic418967fa.accept_17_11_7_1_1_7023 45 75 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 188
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 44 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 188 (accept_3_2 43 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 188 (accept_3_2 40 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 75 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 188 (accept_3_2 37 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 188 (accept_3_2 34 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 188 (accept_3_2 31 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 188 (accept_3_2 28 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 188 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 75 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 188
  (Polychromatic418967fa.accept_16_10_11_12_1_4835 26 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 75 188 (accept_3_2 25 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 75 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 75 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 188 (accept_3_2 22 75 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 188 (Polychromatic418967fa.accept_11_10_9_1_1_2186
  21 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 188 (accept_3_2 19 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 188 (accept_3_2 16 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 75 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 188 (accept_3_2 13 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 188 (accept_3_2 10 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 188 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 75 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 188 (accept_3_2 7 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  188 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 188 (accept_3_2 4 75 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 188 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 75 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  75 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 188 (accept_3_2 1 75 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 188 (allA_succ_of_accept
  73 74 188 (accept_3_2 73 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 188 2 36 37 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 188
  (Polychromatic418967fa.accept_12_11_2_8_1_511 71 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 188 2 35 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 74 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 74 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 188 2 34 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 188 (accept_3_2 67 74 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 188 2 33 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 74 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 188 2 32 37 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 188
  (Polychromatic418967fa.accept_17_12_6_1_1_4517 63 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 188 2 31 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 74 188 (accept_3_2 61 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74
  188 2 30 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  74 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 74 188 2 29 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 74 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 74 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 74 188 2 28 37 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 74 188 (accept_3_2 55 74 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74 188 2 27 37 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 74 188
  (Polychromatic418967fa.accept_12_5_2_8_1_172 53 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 74 188 2 26 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 74 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 74 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 188 2 25 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 188 (accept_3_2 49 74 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 188 2 24 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 74 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 188 2 23 37 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 188 2 22 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 74 188 (accept_3_2 43 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74
  188 2 21 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  74 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 74 188 2 20 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 74 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 74 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 188 2 19 37 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 188 (accept_3_2 37 74 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 188 2 18 37 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 188
  (Polychromatic418967fa.accept_12_11_2_8_1_511 35 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 74 188 2 17 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 74 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 74 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 188 2 16 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 188 (accept_3_2 31 74 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 188 2 15 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 188 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 74 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 188 2 14 37 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 188
  (Polychromatic418967fa.accept_13_1_9_6_1_146 27 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 188 2 13 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 74 188 (accept_3_2 25 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74
  188 2 12 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  74 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 74 188 2 11 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 74 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 74 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 188 2 10 37 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 188 (accept_3_2 19 74 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 188 2 9 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 74 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 188 2 8 37 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 188
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 188 2 7 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 188 (accept_3_2 13 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  188 2 6 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 188 2 5 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 74 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 188 2 4 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 188 (accept_3_2 7 74 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 188 2 3 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 74 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 188 2 2 37 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 188 2 1 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 188 (accept_3_2 1 74 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 188 (allA_of_3_0 73 73 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 188 (allA_succ_of_accept 71 72 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 188 2 35 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 72 188 (Polychromatic418967fa.accept_13_4_7_6_1_2359 69 72 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 188 4 17 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 188 (accept_3_2 67 72 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 188 2 33 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 72 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 188 4 16 18 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 188
  (Polychromatic418967fa.accept_15_3_12_8_1_738 63 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 188 2 31 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 72 188 (accept_3_2 61 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72
  188 4 15 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  72 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 72 188 2 29 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 72 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 72 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 188 4 14 18 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 188 (accept_3_2 55 72 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 188 2 27 36 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 188 4 13 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 72 188 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 72 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 188 2 25 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 188 (accept_3_2 49 72 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 188 4 12 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 188 (Polychromatic418967fa.accept_16_15_8_12_1_2737 47 72
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 188 2 23 36 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 188 4 11 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 188 (accept_3_2 43 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  188 2 21 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  72 188 (Polychromatic418967fa.accept_15_11_12_8_1_739 41 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 188 4 10 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 72 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 72 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 188 2 19 36 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 188 (accept_3_2 37 72 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 188 4 9 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 35
  72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 188 2 17 36 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 188
  (Polychromatic418967fa.accept_15_3_12_8_1_738 33 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 188 4 8 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 188 (accept_3_2 31 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  188 2 15 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  72 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 188 4 7 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 188 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 72 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 188 2 13 36 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 188 (accept_3_2 25 72 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 188 4 6 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 188 (Polychromatic418967fa.accept_16_7_8_12_1_4902 23 72 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 188 2 11 36 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 188
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 21 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 188 4 5 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 188 (accept_3_2 19 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  188 2 9 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 188 4 4 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 188 2 7 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 188 (accept_3_2 13 72 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 188 4 3 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 72 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 188 2 5 36 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 188
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 188 4 2 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 188 (accept_3_2 7 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 188
  2 3 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  188 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 72 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 188 4 1 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 72 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 188 2 1 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 188 (accept_3_2 1 72 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 188
  (allA_succ_of_accept 70 71 188 (accept_3_2 70 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 188 (accept_3_2 67 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 188 (Polychromatic418967fa.accept_16_2_7_12_1_3793 66 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 188
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 188 (accept_3_2 64 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 188 (accept_3_2 61 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 188 (Polychromatic418967fa.accept_17_9_3_1_1_2275 60 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 188
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 188 (accept_3_2 58 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 188 (Polychromatic418967fa.accept_16_8_7_12_1_7207 56 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 188 (accept_3_2 55 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 71 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 188
  (Polychromatic418967fa.accept_10_3_1_8_1_132 53 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 188 (accept_3_2 52 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 188 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 188 (accept_3_2 49 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 188 (Polychromatic418967fa.accept_15_3_11_8_1_4186 48 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 188 (accept_3_2 46 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 188 (accept_3_2 43 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 188 (Polychromatic418967fa.accept_15_12_11_8_1_1392 42 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 188
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 41 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 188 (accept_3_2 40 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 188 (accept_3_2 37 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 188 (Polychromatic418967fa.accept_16_4_7_12_1_2734 36 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 188
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 188 (accept_3_2 34 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 188 (Polychromatic418967fa.accept_17_15_3_1_1_9696 32 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 188 (accept_3_2 31 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 71 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 188
  (Polychromatic418967fa.accept_10_9_1_8_1_755 29 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 188 (accept_3_2 28 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 188 (accept_3_2 25 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 188 (Polychromatic418967fa.accept_16_8_7_12_1_7207 24 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 188
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 188 (accept_3_2 22 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 188 (Polychromatic418967fa.accept_15_5_11_8_1_1391 20 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 188 (accept_3_2 19 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 188 (Polychromatic418967fa.accept_15_3_11_8_1_4186 18 71
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 188
  (Polychromatic418967fa.accept_11_6_5_1_1_586 17 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 188 (accept_3_2 16 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 188 (accept_3_2 13 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 188
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 188 (accept_3_2 10 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 188 (Polychromatic418967fa.accept_16_8_7_12_1_7207 8 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 188 (accept_3_2 7 71 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 188 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 71 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 188 (accept_3_2 4 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 71 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 188 (accept_3_2 1 71 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 188
  (allA_of_3_0 70 70 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 188 (allA_succ_of_accept 68 69 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 188 (accept_3_2 67 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 188 (accept_3_2 64 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 188 (Polychromatic418967fa.accept_13_11_4_6_1_1006 63 69 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 188
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 62 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 188 (accept_3_2 61 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 188 (Polychromatic418967fa.accept_19_3_12_17_1_6585 60 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 188 (accept_3_2 58 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 69 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 188 (accept_3_2 55 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 188 (accept_3_2 52 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 188 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 69 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 188 (accept_3_2 49 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 188 (accept_3_2 46 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 188 (Polychromatic418967fa.accept_21_3_6_20_1_9278 45 69 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 188
  (Polychromatic418967fa.accept_10_4_9_8_1_125 44 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 188 (accept_3_2 43 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 188 (accept_3_2 40 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 69 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 188 (accept_3_2 37 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 188 (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 188 (accept_3_2 34 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 69 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 188 (accept_3_2 31 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 188 (accept_3_2 28 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 188 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 69 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 188
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 188 (accept_3_2 25 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 188 (accept_3_2 22 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 188
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 188 (accept_3_2 19 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 188 (accept_3_2 16 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 188 (Polychromatic418967fa.accept_13_2_4_6_1_2356 15 69 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 188 (accept_3_2 13 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 188 (accept_3_2 10 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 69 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 188
  (Polychromatic418967fa.accept_16_8_5_12_1_3812 8 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 188 (accept_3_2 7 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  188 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 188 (accept_3_2 4 69 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 69 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  69 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 188 (accept_3_2 1 69 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 188 (allA_succ_of_accept 67 68
  188 (accept_3_2 67 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 188 2 33 34 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 188 4 16 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 188 (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 68 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 188 2 31 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 188 (accept_3_2 61 68 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 188 4 15 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 188 (Polychromatic418967fa.accept_16_11_4_12_1_1760 59 68
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 188 2 29 34 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 188 4 14 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 188 (accept_3_2 55 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  188 2 27 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  68 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 188 4 13 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 68 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 188 2 25 34 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 188 (accept_3_2 49 68 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 188 4 12 17 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 188 2 23 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 68 188 (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 68 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 188 4 11 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 188 (accept_3_2 43 68 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 188 2 21 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 188 (Polychromatic418967fa.accept_14_13_12_6_1_2735 41 68
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 188 4 10 17 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 188 2 19 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 68 188 (accept_3_2 37 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68
  188 4 9 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  68 188 (Polychromatic418967fa.accept_13_9_3_6_1_1661 35 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 68 188 2 17 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 68 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 68 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 188 4 8 17 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 188 (accept_3_2 31 68 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 188 2 15 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 29
  68 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 188 4 7 17 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 188
  (Polychromatic418967fa.accept_13_1_3_6_1_158 27 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 188 2 13 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 68 188 (accept_3_2 25 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68
  188 4 6 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  68 188 (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 68 188 2 11 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 68 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 68 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 188 4 5 17 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 188 (accept_3_2 19 68 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 188 2 9 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 68 188 (Polychromatic418967fa.accept_16_1_4_12_1_376 17 68 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 188 4 4 17 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 188 2 7 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 188 (accept_3_2 13 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  188 4 3 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 188 2 5 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 188 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 68 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 188 4 2 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 188 (accept_3_2 7 68 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 188 2 3 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 188 (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 68 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 188 4 1 17 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 188 2 1 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 188 (accept_3_2 1 68 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 188 (allA_of_3_0 67 67 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 188 (allA_succ_of_accept 65 66 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 188 2 32 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 66 188 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 66 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 188 2 31 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 188 (accept_3_2 61 66 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 188 2 30 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 66 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 188 2 29 33 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 188 2 28 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 66 188 (accept_3_2 55 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66
  188 2 27 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  66 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 66 188 2 26 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 66 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 66 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 188 2 25 33 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 188 (accept_3_2 49 66 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 188 2 24 33 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 188 2 23 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 66 188 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 66 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 188 2 22 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 188 (accept_3_2 43 66 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 188 2 21 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 66 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 188 2 20 33 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 188 2 19 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 66 188 (accept_3_2 37 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66
  188 2 18 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  66 188 (Polychromatic418967fa.accept_13_9_1_6_1_510 35 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 66 188 2 17 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 66 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 66 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 188 2 16 33 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 188 (accept_3_2 31 66 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 188 2 15 33 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 188 2 14 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 66 188 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 66 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 188 2 13 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 188 (accept_3_2 25 66 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 188 2 12 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 66 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 188 2 11 33 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 188 2 10 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 188 (accept_3_2 19 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66
  188 2 9 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  66 188 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 66 188 2 8 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 66 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 66 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 188 2 7 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 188 (accept_3_2 13 66 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 188 2 6 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 66 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 66 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 188 2 5 33 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 188 2 4 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 188 (accept_3_2 7 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 188
  2 3 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66
  188 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 66 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 188 2 2 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 66 188 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 66 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 188 2 1 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 188 (accept_3_2 1 66 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 188
  (allA_succ_of_accept 64 65 188 (accept_3_2 64 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 188 (accept_3_2 61 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 65 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 188 (accept_3_2 58 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 188 (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 65 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 188 (accept_3_2 55 65 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 188 (Polychromatic418967fa.accept_19_16_8_17_1_5148 54 65
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 188 (accept_3_2 52 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 188 (accept_3_2 49 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 65 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 188
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 188 (accept_3_2 46 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 188 (Polychromatic418967fa.accept_15_14_5_8_1_3175 44 65 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 188 (accept_3_2 43 65 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 65 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 188 (accept_3_2 40 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 188 (accept_3_2 37 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 65 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 188
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 188 (accept_3_2 34 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 188 (accept_3_2 31 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 65 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 188 (accept_3_2 28 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 188 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 188 (accept_3_2 25 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 188 (accept_3_2 22 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 188 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 188 (accept_3_2 19 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 65 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 188 (accept_3_2 16 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 188 (accept_3_2 13 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 65 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 188 (accept_3_2 10 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 188 (accept_3_2 7 65 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 65 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 188
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 188 (accept_3_2 4 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 65 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 188 (accept_3_2 1 65 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 188
  (allA_of_3_0 64 64 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 188 (allA_succ_of_accept 62 63 188
  (Polychromatic418967fa.accept_27_8_9_26_1_4766 62 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 188 (accept_3_2 61 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 188 (Polychromatic418967fa.accept_13_8_11_6_1_1035 60 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 188 (accept_3_2 58 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 188 (Polychromatic418967fa.accept_13_5_11_6_1_505 57 63 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 188
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 188 (accept_3_2 55 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 188 (accept_3_2 52 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 188
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 188 (accept_3_2 49 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 188 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 188 (accept_3_2 46 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 188 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 63 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 188
  (Polychromatic418967fa.accept_13_5_11_6_1_505 44 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 188 (accept_3_2 43 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 188 (accept_3_2 40 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 188 (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 63 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 188
  (Polychromatic418967fa.accept_20_18_3_8_1_7903 38 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 188 (accept_3_2 37 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 188 (accept_3_2 34 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 188 (Polychromatic418967fa.accept_17_16_12_1_1_5785 33 63 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 188
  (Polychromatic418967fa.accept_17_15_12_1_1_3365 32 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 188 (accept_3_2 31 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 188 (accept_3_2 28 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 188
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 188 (accept_3_2 25 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 188 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 188 (accept_3_2 22 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 188 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 63 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 188
  (Polychromatic418967fa.accept_15_5_3_8_1_748 20 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 188 (accept_3_2 19 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 188 (accept_3_2 16 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 188 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 63 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 188
  (Polychromatic418967fa.accept_20_14_3_8_1_4914 14 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 188 (accept_3_2 13 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 188 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 188 (accept_3_2 10 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 188 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 63 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 188
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 8 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 188 (accept_3_2 7 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 188 (accept_3_2 4 63 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 188
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 2 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 188 (accept_3_2 1 63 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 188 (allA_succ_of_accept 61 62 188
  (accept_3_2 61 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 188 2 30 31 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 188
  (Polychromatic418967fa.accept_12_11_2_8_1_511 59 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 188 2 29 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 188 (Polychromatic418967fa.accept_13_5_10_6_1_2361 57 62 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 188 2 28 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 188 (accept_3_2 55 62 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 188 2 27 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 62 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 188 2 26 31 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 188
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 51 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 188 2 25 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 188 (accept_3_2 49 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  188 2 24 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 188 2 23 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 62 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 188 2 22 31 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 188 (accept_3_2 43 62 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 188 2 21 31 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 188
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 188 2 20 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 188 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 62 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 188 2 19 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 188 (accept_3_2 37 62 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 188 2 18 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 62 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 188 2 17 31 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 188
  (Polychromatic418967fa.accept_19_14_5_17_1_6542 33 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 188 2 16 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 188 (accept_3_2 31 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  188 2 15 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 188 2 14 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 188 (Polychromatic418967fa.accept_17_10_11_1_1_5784 27 62 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 188 2 13 31 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 188 (accept_3_2 25 62 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 188 2 12 31 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 188
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 188 2 11 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 188 (Polychromatic418967fa.accept_15_6_2_8_1_2223 21 62 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 188 2 10 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 188 (accept_3_2 19 62 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 188 2 9 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 188 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 62 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 188 2 8 31 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 188
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 188 2 7 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 188 (accept_3_2 13 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  188 2 6 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 188 2 5 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 188 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 62 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 188 2 4 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 188 (accept_3_2 7 62 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 188 2 3 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 62 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 188 2 2 31 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 188
  (Polychromatic418967fa.accept_13_3_10_6_1_2382 3 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 188 2 1 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 188 (accept_3_2 1 62 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 188 (allA_of_3_0 61 61 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 188 (allA_succ_of_accept 59 60 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 188 2 29 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 60 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 188 4 14 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 188 (accept_3_2 55 60 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 188 2 27 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 188 (Polychromatic418967fa.accept_13_1_8_6_1_1016 53 60 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 188 4 13 15 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 188 2 25 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 188 (accept_3_2 49 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60
  188 4 12 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  60 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 60 188 2 23 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 60 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 60 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 188 4 11 15 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 188 (accept_3_2 43 60 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 188 2 21 30 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 188 4 10 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 188 2 19 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 188 (accept_3_2 37 60 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 188 4 9 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 60 188 (Polychromatic418967fa.accept_19_16_3_17_1_6575 35 60 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 188 2 17 30 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 188
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 188 4 8 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 188 (accept_3_2 31 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  188 2 15 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 188 4 7 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 188 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 60 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 188 2 13 30 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 188 (accept_3_2 25 60 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 188 4 6 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 188 2 11 30 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 188
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 188 4 5 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 188 (accept_3_2 19 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  188 2 9 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 188 4 4 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 188 (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 60 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 188 2 7 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 188 (accept_3_2 13 60 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 188 4 3 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 60 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 188 2 5 30 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 188 4 2 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 188 (accept_3_2 7 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 188
  2 3 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60
  188 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 60 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 188 4 1 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 188 2 1 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 188 (accept_3_2 1 60 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 188
  (allA_succ_of_accept 58 59 188 (accept_3_2 58 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 188 (accept_3_2 55 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 59 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 188 (accept_3_2 52 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 188 (accept_3_2 49 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 59 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 188
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 188 (accept_3_2 46 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 188 (accept_3_2 43 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 188
  (Polychromatic418967fa.accept_10_1_9_8_1_123 41 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 188 (accept_3_2 40 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 188 (accept_3_2 37 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 188 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 59 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 188
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 35 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 188 (accept_3_2 34 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 188 (accept_3_2 31 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 59 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 188 (accept_3_2 28 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 188 (accept_3_2 25 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 188 (accept_3_2 22 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 188 (accept_3_2 19 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 59 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 188
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 188 (accept_3_2 16 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 188 (accept_3_2 13 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 59 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 188 (accept_3_2 10 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 188 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 188 (accept_3_2 7 59 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 59 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 188
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 188 (accept_3_2 4 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 59 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 188 (accept_3_2 1 59 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 188 (allA_of_3_0
  58 58 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 188 (allA_succ_of_accept 56 57 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 188 (accept_3_2 55 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 188 (accept_3_2 52 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 57 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 188 (accept_3_2 49 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 188 (Polychromatic418967fa.accept_15_3_12_8_1_738 48 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 188 (accept_3_2 46 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 57 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 188
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 188 (accept_3_2 43 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 188 (accept_3_2 40 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 188 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 57 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 188 (accept_3_2 37 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 188 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 188 (accept_3_2 34 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 188 (accept_3_2 31 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 188 (accept_3_2 28 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 188 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 57 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 188 (accept_3_2 25 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 188 (accept_3_2 22 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 188 (accept_3_2 19 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 188 (accept_3_2 16 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 188 (accept_3_2 13 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 188 (accept_3_2 10 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 188
  (Polychromatic418967fa.accept_16_8_9_12_1_1737 8 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 188 (accept_3_2 7 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  188 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 188 (accept_3_2 4 57 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 188 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 57 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  57 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 188 (accept_3_2 1 57 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 188)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 188 (allA_succ_of_accept 55 56 188 (accept_3_2 55 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 188 2 27 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 188 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 56 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 188 4 13 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 51
  56 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 188 2 25 28 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 188 (accept_3_2 49
  56 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 188 4 12 14 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 188
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 47 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 188 2 23 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 188 (Polychromatic418967fa.accept_16_13_8_12_1_2723 45 56 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 188 4 11 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 188 (accept_3_2 43 56 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 188 2 21 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 188 4 10 14 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 188
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 188 2 19 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 188 (accept_3_2 37 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  188 4 9 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 188 (Polychromatic418967fa.accept_13_9_4_6_1_1005 35 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 188 2 17 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 56 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 188 4 8 14 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 188 (accept_3_2 31 56 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 188 2 15 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 188 (Polychromatic418967fa.accept_16_13_8_12_1_2723
  29 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 188 4 7 14 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 188
  (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 56 188 2 13 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 56 188 (accept_3_2 25 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56
  188 4 6 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  56 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 56 188 2 11 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 56 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 56 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 188 4 5 14 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 188 (accept_3_2 19 56 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 188 2 9 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 56 188 (Polychromatic418967fa.accept_16_1_8_12_1_405 17 56 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 188 4 4 14 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 188
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 188 2 7 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 188 (accept_3_2 13 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56
  188 4 3 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  56 188 (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 188 2 5 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 188 (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 56 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 188 4 2 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 188 (accept_3_2 7 56 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 188 2 3 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 56 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 188 4 1 14 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 188
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 56 188 2 1 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 56 188 (accept_3_2 1 56 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 188 (allA_of_3_0 55 55 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 54 188 (allA_succ_of_accept 53 54 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 188 2 26 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 188 (Polychromatic418967fa.accept_12_3_6_8_1_969 51 54 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 188 2 25 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 188 (accept_3_2 49 54 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 188 2 24 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 188 (Polychromatic418967fa.accept_13_8_2_6_1_2385 47 54 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 188 2 23 27 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 188 2 22 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 188 (accept_3_2 43 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54
  188 2 21 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  54 188 (Polychromatic418967fa.accept_14_13_12_6_1_2735 41 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 188 2 20 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 54 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 188 2 19 27 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 188 (accept_3_2 37 54 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 188 2 18 27 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 188
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 188 2 17 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 54 188 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 188 2 16 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 188 (accept_3_2 31 54 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 188 2 15 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 54 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 188 2 14 27 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 188 2 13 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 188 (accept_3_2 25 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54
  188 2 12 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  54 188 (Polychromatic418967fa.accept_13_10_2_6_1_1044 23 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 54 188 2 11 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 54 188 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 188 2 10 27 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 188 (accept_3_2 19 54 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 188 2 9 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 188 (Polychromatic418967fa.accept_13_4_2_6_1_1043
  17 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 188 2 8 27 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 188 2 7 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 188 (accept_3_2 13 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54
  188 2 6 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  54 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 188 2 5 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 188 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 54 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 188 2 4 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 188 (accept_3_2 7 54 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 188 2 3 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 54 188 (Polychromatic418967fa.accept_20_5_14_8_1_6391 5 54 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 188 2 2 27 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 188 2 1 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 188 (accept_3_2 1 54 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  188)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 188 (allA_succ_of_accept 52 53 188 (accept_3_2
  52 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 188
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 188 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 53 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 188 (accept_3_2 49 53 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 188 (Polychromatic418967fa.accept_13_9_1_6_1_510 48 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 188 (accept_3_2 46 53
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 188 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 53 188 (accept_3_2 43 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  53 188 (Polychromatic418967fa.accept_13_3_1_6_1_509 42 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 53 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 188 (accept_3_2 40 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 188 (accept_3_2 37 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 188 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 188 (accept_3_2 34 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 188
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 188 (accept_3_2 31 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 188 (Polychromatic418967fa.accept_13_3_1_6_1_509 29 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 188 (accept_3_2 28 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 188
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 188 (accept_3_2 25 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 188 (accept_3_2 22 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 188
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 20 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 188 (accept_3_2 19 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 188 (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 188 (accept_3_2 16 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 188 (accept_3_2 13 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 188 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 188 (accept_3_2 10 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 188
  (Polychromatic418967fa.accept_13_8_1_6_1_997 8 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 188 (accept_3_2 7 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 53 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 188 (accept_3_2 4 53 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 53 188 (accept_3_2 1 53 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53
  188))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 188 (allA_of_3_0 52 52 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 51 188 (allA_succ_of_accept 50 51 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 51
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 188 (accept_3_2 49 51 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 48
  51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 51 188 (accept_3_2 46 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  51 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 51 188 (Polychromatic418967fa.accept_13_5_12_6_1_508 44 51 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 188 (accept_3_2 43 51 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 51 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 188 (accept_3_2 40 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  51 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 51 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 51 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 188 (accept_3_2 37 51 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 188 (accept_3_2 34 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  51 188 (Polychromatic418967fa.accept_10_3_1_8_1_132 33 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 51 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 51 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 188 (accept_3_2 31 51 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 188 (accept_3_2 28 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  51 188 (Polychromatic418967fa.accept_21_6_9_20_1_3190 27 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 51 188 (Polychromatic418967fa.accept_16_10_3_12_1_1758 26 51 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 188 (accept_3_2 25 51 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 188 (accept_3_2 22 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  51 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 51 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 51 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 188 (accept_3_2 19 51 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 51 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 188 (accept_3_2 16 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  51 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 51 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 51 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 188 (accept_3_2 13 51 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 51 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 188 (accept_3_2 10 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  51 188 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 51 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 51 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 188 (accept_3_2 7 51 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 188 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 51 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 188 (accept_3_2 4 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51
  188 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 51 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 188 (accept_3_2 1 51 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 51 188))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 188 (allA_succ_of_accept
  49 50 188 (accept_3_2 49 50 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 188 2 24 25 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 50 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 188 2 23 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 50 188 (Polychromatic418967fa.accept_20_5_10_8_1_6397 45 50 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 188 2 22 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 188 (accept_3_2 43 50 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 188 2 21 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 50 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 188 2 20 25 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 50 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 188 2 19 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 50 188 (accept_3_2 37 50 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50
  188 2 18 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  50 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 50 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 50 188 2 17 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 50 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 50 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 188 2 16 25 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 188 (accept_3_2 31 50 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 188 2 15 25 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 188 2 14 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 50 188 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 50 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 188 2 13 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 188 (accept_3_2 25 50 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 188 2 12 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 50 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 188 2 11 25 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 50 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 188 2 10 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 50 188 (accept_3_2 19 50 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50
  188 2 9 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  50 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 50 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 50 188 2 8 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 50 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 50 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 188 2 7 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 188 (accept_3_2 13 50 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 188 2 6 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 50 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 50 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 188 2 5 25 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 188
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 50 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 50 188 2 4 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 50 188 (accept_3_2 7 50 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 188
  2 3 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 50
  188 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 50 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 50 188 2 2 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 50 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 50 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 188 2 1 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 188 (accept_3_2 1 50 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 188)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 188 (allA_of_3_0 49 49
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 188 (allA_succ_of_accept 47 48 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 48 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 188 2 23 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 48 188 (Polychromatic418967fa.accept_19_7_10_17_1_8088 45 48 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 188 4 11 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 188 (accept_3_2 43 48 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 188 2 21 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 188 4 10 12 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 188
  (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 48 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 48 188 2 19 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 48 188 (accept_3_2 37 48 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48
  188 4 9 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  48 188 (Polychromatic418967fa.accept_15_5_3_8_1_748 35 48 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 48 188 2 17 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 48 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 188 4 8 12 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 188 (accept_3_2 31 48 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 188 2 15 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 29
  48 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 188 4 7 12 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 188
  (Polychromatic418967fa.accept_13_1_9_6_1_146 27 48 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 188 2 13 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 188 (accept_3_2 25 48 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48
  188 4 6 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  48 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 48 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 48 188 2 11 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 48 188 (Polychromatic418967fa.accept_17_4_14_1_1_1363 21 48 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 188 4 5 12 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 188 (accept_3_2 19 48 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 188 2 9 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 188 (Polychromatic418967fa.accept_13_4_9_6_1_2376 17 48 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 188 4 4 12 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 188
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 48 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 48 188 2 7 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 188 (accept_3_2 13 48 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48
  188 4 3 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  48 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 48 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 48 188 2 5 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 48 188 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 48 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 188 4 2 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 188 (accept_3_2 7 48 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 188 2 3 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 48 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 188 4 1 12 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 188
  (Polychromatic418967fa.accept_13_3_9_6_1_502 3 48 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 48 188 2 1 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 188 (accept_3_2 1 48 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  188)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 188 (allA_succ_of_accept 46 47 188 (accept_3_2 46 47
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 188 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 188
  (Polychromatic418967fa.accept_19_6_9_17_1_5214 44 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 188 (accept_3_2 43 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 47 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 188 (accept_3_2 40 47 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 188
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 188 (accept_3_2 37 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 47 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 188 (accept_3_2 34 47 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 188 (accept_3_2 31 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 47 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 188 (accept_3_2 28 47 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 188
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 188 (accept_3_2 25 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 188 (accept_3_2 22 47 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 188
  (Polychromatic418967fa.accept_16_4_15_12_1_1745 20 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 188 (accept_3_2 19 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 188 (Polychromatic418967fa.accept_20_17_7_8_1_7919 17 47 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 188 (accept_3_2 16 47 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 188 (accept_3_2 13 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 188 (accept_3_2 10 47 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 188 (accept_3_2 7 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  188 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 47 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 188 (accept_3_2 4 47 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 188 (Polychromatic418967fa.accept_11_2_3_1_1_244 2
  47 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 188 (accept_3_2 1 47 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 188))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  188 (allA_of_3_0 46 46 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 188 (allA_succ_of_accept 44 45 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 188 (accept_3_2 43 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 188 (accept_3_2 40 45 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 45 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 188
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 188 (accept_3_2 37 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 188 (Polychromatic418967fa.accept_16_4_13_12_1_1740 36 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 188 (accept_3_2 34 45 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 45 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 188 (accept_3_2 31 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 188 (accept_3_2 28 45 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 188 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 45 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 188
  (Polychromatic418967fa.accept_16_10_13_12_1_4873 26 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 45 188 (accept_3_2 25 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 45 188 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 45 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 188 (accept_3_2 22 45 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 188 (Polychromatic418967fa.accept_18_3_9_8_1_2977
  21 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 188
  (Polychromatic418967fa.accept_16_4_13_12_1_1740 20 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 188 (accept_3_2 19 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 188 (accept_3_2 16 45 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 188 (Polychromatic418967fa.accept_16_15_13_12_1_1787 15 45 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 188
  (Polychromatic418967fa.accept_20_14_5_8_1_4870 14 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 188 (accept_3_2 13 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 188 (accept_3_2 10 45 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 188
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 8 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 188 (accept_3_2 7 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  188 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 45 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 188 (accept_3_2 4 45 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 188 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 45 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 45
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 188 (accept_3_2 1 45 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 188))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  188 (allA_succ_of_accept 43 44 188 (accept_3_2 43 44 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 188 2 21 22 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 44 188 (Polychromatic418967fa.accept_17_7_10_1_1_4488 41 44 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 44 188 4 10 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 44 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 44 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 188 2 19 22 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 188 (accept_3_2 37 44 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 188 4 9 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 188 (Polychromatic418967fa.accept_15_5_14_8_1_1376
  35 44 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 188 2 17 22 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 188
  (Polychromatic418967fa.accept_23_10_21_4_1_10796 33 44 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 44 188 4 8 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 44 188 (accept_3_2 31 44 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 44 188 2 15 22 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 44 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 44 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 188 4 7 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 188 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 44 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 188 2 13 22 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 188 (accept_3_2 25
  44 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 188 4 6 11 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 188
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 23 44 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 188 2 11 22 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 188 (Polychromatic418967fa.accept_15_6_14_8_1_245 21 44 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 188 4 5 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 188 (accept_3_2 19 44 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 44 188 2 9 22 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 44 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 44 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 188 4 4 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  44 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 188 2 7 22 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 188 (accept_3_2 13
  44 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 188 4 3 11 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 44 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 44 188 2 5 22 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 44 188 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 44 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 188 4 2 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 188 (accept_3_2 7 44 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 44 188 2 3 22 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 44 188 (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 44 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 188 4 1 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 44
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 188 2 1 22 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 188 (accept_3_2 1 44
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 188)))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  43 188 (allA_of_3_0 43 43 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 188 (allA_succ_of_accept 41 42
  188 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 188 2 20 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 42 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 188 2 19 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 188 (accept_3_2 37 42 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 188 2 18 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 42 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 188 2 17 21 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 188 2 16 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 188 (accept_3_2 31 42 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42
  188 2 15 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  42 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 42 188 2 14 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 42 188 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 42 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 188 2 13 21 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 188 (accept_3_2 25 42 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 188 2 12 21 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 188
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 188 2 11 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 42 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 42 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 188 2 10 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 188 (accept_3_2 19 42 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 188 2 9 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 42 188 (Polychromatic418967fa.accept_22_17_20_12_1_10795 17 42 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 188 2 8 21 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 188
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 42 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 42 188 2 7 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 188 (accept_3_2 13 42 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42
  188 2 6 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  42 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 42 188 2 5 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 42 188 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 188 2 4 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 188 (accept_3_2 7 42 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 188 2 3 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 42 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 188 2 2 21 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 188
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 42 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 42 188 2 1 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 188 (accept_3_2 1 42 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  188)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 188 (allA_succ_of_accept 40 41 188 (accept_3_2 40 41 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39
  41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 188 (accept_3_2 37 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 188 (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 188 (Polychromatic418967fa.accept_13_9_2_6_1_514 35 41 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 188 (accept_3_2 34 41 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 188
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 32 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 188 (accept_3_2 31 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 41 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 188 (accept_3_2 28 41 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 188
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 188 (accept_3_2 25 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 188 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 41 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 188 (accept_3_2 22 41 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 188 (accept_3_2 19 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 188 (Polychromatic418967fa.accept_15_3_11_8_1_4186 18 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 188 (Polychromatic418967fa.accept_13_4_2_6_1_1043 17 41 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 188 (accept_3_2 16 41 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 188 (accept_3_2 13 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 41 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 188 (accept_3_2 10 41 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 188
  (Polychromatic418967fa.accept_13_8_2_6_1_2385 8 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 188 (accept_3_2 7 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  188 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 41 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 188 (accept_3_2 4 41 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 41
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 188 (accept_3_2 1 41 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 188))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 188
  (allA_of_3_0 40 40 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 188 (allA_succ_of_accept 38 39 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 188 (accept_3_2 37 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 188 (Polychromatic418967fa.accept_16_4_7_12_1_2734 36 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 188 (accept_3_2 34 39 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 39 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 188 (accept_3_2 31 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 188 (accept_3_2 28 39 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 39 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 188
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 188 (accept_3_2 25 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 188 (accept_3_2 22 39 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 188 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 39 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 188 (accept_3_2 19 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 188 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 188 (accept_3_2 16 39 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 188 (accept_3_2 13 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 188 (accept_3_2 10 39 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 39 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 188
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 8 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 188 (accept_3_2 7 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  188 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 188 (accept_3_2 4 39 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 39 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  39 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 188 (accept_3_2 1 39 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 188))))))))))))))))))))))))))))))))))))))) (allB_succ 38 188
  (allA_succ_of_accept 37 38 188 (accept_3_2 37 38 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  188 2 18 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 188 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 38 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 188 2 17 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 38 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 188 2 16 19 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 188 (accept_3_2 31 38 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 188 2 15 19 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 188
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 38 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 188 2 14 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 188 (Polychromatic418967fa.accept_22_5_16_12_1_7590 27 38 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 188 2 13 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 188 (accept_3_2 25 38 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 188 2 12 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 38 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 188 2 11 19 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 188
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 38 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 188 2 10 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 188 (accept_3_2 19 38 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  188 2 9 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 188 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 38 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 188 2 8 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 38 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 188 2 7 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 188 (accept_3_2 13 38 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 188 2 6 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 38 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 188 2 5 19 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 38 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 188 2 4 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 188 (accept_3_2 7 38 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 188
  2 3 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  188 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 38 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 188 2 2 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 38 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 188 2 1 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 188 (accept_3_2 1 38 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 188)))))))))))))))))))))))))))))))))))))) (allB_succ 37 188 (allA_of_3_0 37 37 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 188 (allA_succ_of_accept 35 36 188
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 36 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 188 2 17 18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 188 4 8 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 188 (accept_3_2 31 36 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 36 188 2 15 18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 36 188 (Polychromatic418967fa.accept_13_3_10_6_1_2382 29 36 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 188 4 7 9 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 188
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 27 36 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 188 2 13 18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 188 (accept_3_2 25 36 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36
  188 4 6 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  36 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 188 2 11 18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 188 (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 36 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 188 4 5 9 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 188 (accept_3_2 19 36 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 188 2 9 18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 188 (Polychromatic418967fa.accept_13_4_10_6_1_989 17 36 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 188 4 4 9 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 188
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 36 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 188 2 7 18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 188 (accept_3_2 13 36 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36
  188 4 3 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  36 188 (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 36 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 188 2 5 18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 188 4 2 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 188 (accept_3_2 7 36 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 188 2 3 18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 36 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 188 4 1 9 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 188
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 36 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 188 2 1 18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 188 (accept_3_2 1 36 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  188)))))))))))))))))))))))))))))))))))) (allB_succ 35 188 (allA_succ_of_accept 34 35 188 (accept_3_2 34 35 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  35 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 188
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 188 (accept_3_2 31 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 188 (Polychromatic418967fa.accept_13_4_9_6_1_2376 30 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 188 (Polychromatic418967fa.accept_13_3_9_6_1_502 29 35 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 188 (accept_3_2 28 35 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 188
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 188 (accept_3_2 25 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 188 (Polychromatic418967fa.accept_16_8_3_12_1_1819 24 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 35 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 188 (accept_3_2 22 35 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 35 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 188
  (Polychromatic418967fa.accept_13_7_9_6_1_148 20 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 188 (accept_3_2 19 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 188 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 188 (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 35 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 188 (accept_3_2 16 35 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 188
  (Polychromatic418967fa.accept_11_3_2_1_1_994 14 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 188 (accept_3_2 13 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 188 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 188 (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 35 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 188 (accept_3_2 10 35 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 188
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 188 (accept_3_2 7 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  188 (Polychromatic418967fa.accept_21_6_14_20_1_4594 6 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 35 188 (Polychromatic418967fa.accept_18_5_17_8_1_2984 5 35 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 188 (accept_3_2 4 35 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 188
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 188 (accept_3_2 1 35 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  188))))))))))))))))))))))))))))))))))) (allB_succ 34 188 (allA_of_3_0 34 34 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 188 (allA_succ_of_accept 32 33 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 33 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 188 (accept_3_2 31 33 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 30
  33 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 188 (accept_3_2 28 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 188 (Polychromatic418967fa.accept_13_1_7_6_1_142 27 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 33 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 188 (accept_3_2 25 33 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 188 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 33 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 188 (accept_3_2 22 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 33 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 188 (accept_3_2 19 33 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 33 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 188 (accept_3_2 16 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 33 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 188 (accept_3_2 13 33 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 188 (accept_3_2 10 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 188 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 33 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 188 (accept_3_2 7 33 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 33 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 188 (accept_3_2 4 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  188 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 33 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 33 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 188 (accept_3_2 1 33 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 188))))))))))))))))))))))))))))))))) (allB_succ 32 188 (allA_succ_of_accept 31 32 188
  (accept_3_2 31 32 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 188 2 15 16 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 188 4 7 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 188 (Polychromatic418967fa.accept_21_6_11_20_1_10794 27 32 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 188 2 13 16 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 188 (accept_3_2 25 32 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 188 4 6 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 32 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 32 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 188 2 11 16 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 32 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 188 4 5 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 188 (accept_3_2 19 32 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  188 2 9 16 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 32 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 188 4 4 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 32 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 188 2 7 16 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 188 (accept_3_2 13 32 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 188 4 3 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 188 2 5 16 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 32 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 188 4 2 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 188 (accept_3_2 7 32 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 188
  2 3 16 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  188 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 32 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 188 4 1 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 32 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 188 2 1 16 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 188 (accept_3_2 1 32 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 188)))))))))))))))))))))))))))))))) (allB_succ 31 188 (allA_of_3_0 31 31 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 188 (allA_succ_of_accept 29 30 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 30 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 188 2 14 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 30 188 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 30 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 188 2 13 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 188 (accept_3_2 25 30 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 188 2 12 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 30 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 188 2 11 15 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 188 2 10 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 188 (accept_3_2 19 30 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30
  188 2 9 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  30 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 30 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 188 2 8 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 30 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 188 2 7 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 188 (accept_3_2 13 30 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 188 2 6 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 30 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 30 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 188 2 5 15 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 188 2 4 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 188 (accept_3_2 7 30 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 188
  2 3 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30
  188 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 30 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 188 2 2 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 30 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 30 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 188 2 1 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 188 (accept_3_2 1 30 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 188)))))))))))))))))))))))))))))) (allB_succ 29 188 (allA_succ_of_accept 28 29 188
  (accept_3_2 28 29 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 188
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 29 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 188 (accept_3_2 25 29 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 29 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 23
  29 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 188 (accept_3_2 22 29
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 188 (Polychromatic418967fa.accept_6_3_5_2_1_12
  21 29 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 188
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 29 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 188 (accept_3_2 19 29 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 188 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 29 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 29 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 188 (accept_3_2 16 29 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 188 (accept_3_2 13 29 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 188 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 29 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 188 (accept_3_2 10 29 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 188
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 8 29 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 188 (accept_3_2 7 29 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  188 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 29 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 188 (accept_3_2 4 29 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  29 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 188 (accept_3_2 1 29 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 188))))))))))))))))))))))))))))) (allB_succ 28 188 (allA_of_3_0
  28 28 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 188 (allA_succ_of_accept 26 27 188
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 27 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 188 (accept_3_2 25 27 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 188 (Polychromatic418967fa.accept_16_8_11_12_1_962 24 27 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 188 (accept_3_2 22 27 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 188 (Polychromatic418967fa.accept_13_8_1_6_1_997 21 27 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 188
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 20 27 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 188 (accept_3_2 19 27 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 27 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 188 (accept_3_2 16 27 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 27 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 188
  (Polychromatic418967fa.accept_17_14_10_1_1_4523 14 27 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 188 (accept_3_2 13 27 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 188 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 27 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 188 (accept_3_2 10 27 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 188 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 27 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 188
  (Polychromatic418967fa.accept_13_8_1_6_1_997 8 27 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 188 (accept_3_2 7 27 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  188 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 27 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 188 (accept_3_2 4 27 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 188 (Polychromatic418967fa.accept_13_3_1_6_1_509 3 27 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 188 (Polychromatic418967fa.accept_13_2_1_6_1_2365 2
  27 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 188 (accept_3_2 1 27 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 188))))))))))))))))))))))))))) (allB_succ 26 188
  (allA_succ_of_accept 25 26 188 (accept_3_2 25 26 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  188 2 12 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 188 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 26 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 188 2 11 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 188 (Polychromatic418967fa.accept_16_5_10_12_1_4904 21 26 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 188 2 10 13 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 188 (accept_3_2 19 26 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 188 2 9 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 17
  26 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 188 2 8 13 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 188
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 26 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 188 2 7 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 188 (accept_3_2 13 26 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  188 2 6 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 26 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 188 2 5 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 188 (Polychromatic418967fa.accept_19_9_7_17_1_3875 9 26 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 188 2 4 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 188 (accept_3_2 7 26 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 188 2 3 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 26 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 188 2 2 13 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 188
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 26 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 188 2 1 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 188 (accept_3_2 1 26 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  188)))))))))))))))))))))))))) (allB_succ 25 188 (allA_of_3_0 25 25 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 188 (allA_succ_of_accept 23 24 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 188 2 11 12 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 188
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 188 4 5 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 188 (accept_3_2 19 24 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  188 2 9 12 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 188 (Polychromatic418967fa.accept_13_4_11_6_1_1033 17 24 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 188 4 4 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 188 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 24 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 188 2 7 12 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 188 (accept_3_2 13 24 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 188 4 3 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 188 2 5 12 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 188 4 2 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 188 (accept_3_2 7 24 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 188
  2 3 12 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  188 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 188 4 1 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 188 2 1 12 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 188 (accept_3_2 1 24 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 188)))))))))))))))))))))))) (allB_succ 23 188 (allA_succ_of_accept 22 23 188 (accept_3_2 22
  23 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 188
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 23 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 188 (accept_3_2 19 23 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 23 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  23 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 188 (accept_3_2 16 23
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 188 (Polychromatic418967fa.accept_6_3_5_2_1_12
  15 23 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 188
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 188 (accept_3_2 13 23 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 23 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 188 (accept_3_2 10 23 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 23 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 188 (accept_3_2 7 23 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  188 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 23 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 188 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 23 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 188 (accept_3_2 4 23 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 188 (accept_3_2 1 23 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 188))))))))))))))))))))))) (allB_succ 22 188 (allA_of_3_0 22 22
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 188 (allA_succ_of_accept 20 21 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 21 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 188 (accept_3_2 19 21 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 21 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 188 (accept_3_2 16 21 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 188
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 21 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 188 (accept_3_2 13 21 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 188 (Polychromatic418967fa.accept_18_12_3_8_1_6817 12 21 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 188 (accept_3_2 10 21 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 188 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 188
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 21 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 188 (accept_3_2 7 21 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  188 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 188 (accept_3_2 4 21 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 188 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 21 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  21 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 188 (accept_3_2 1 21 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 188))))))))))))))))))))) (allB_succ 20 188 (allA_succ_of_accept
  19 20 188 (accept_3_2 19 20 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 188 2 9 10 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 188
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 17 20 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 188 4 4 5 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 20 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 188 2 7 10 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 188 (accept_3_2 13 20 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 188 4 3 5 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 188 (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 20 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 188 2 5 10 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 188 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9
  20 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 188 4 2 5 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 188 (accept_3_2 7 20
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 188 2 3 10 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 20 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 188 4 1 5 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 20 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 188 2 1 10 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 188 (accept_3_2 1 20 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 188)))))))))))))))))))) (allB_succ 19 188 (allA_of_3_0 19 19 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 188 (allA_succ_of_accept 17 18 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 18 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 188 2 8 9 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 18 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 188 2 7 9 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 188 (accept_3_2 13 18 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  188 2 6 9 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 188 (Polychromatic418967fa.accept_13_11_5_6_1_519 11 18 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 188 2 5 9 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 18 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 188 2 4 9 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 188 (accept_3_2 7 18 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 188 2 3 9 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 18 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 188 2 2 9 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 188
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 18 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 188 2 1 9 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 188 (accept_3_2 1 18 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  188)))))))))))))))))) (allB_succ 17 188 (allA_succ_of_accept 16 17 188 (accept_3_2 16 17 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 17 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 188 (accept_3_2 13 17 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 188 (Polychromatic418967fa.accept_24_12_17_20_1_10793 12 17 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 17 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 188 (accept_3_2 10 17 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 188
  (Polychromatic418967fa.accept_16_8_1_12_1_984 8 17 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 188 (accept_3_2 7 17 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  188 (Polychromatic418967fa.accept_15_6_2_8_1_2223 6 17 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 17 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 188 (accept_3_2 4 17 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 17 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 188 (accept_3_2 1 17 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  188))))))))))))))))) (allB_succ 16 188 (allA_of_3_0 16 16 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15
  188 (allA_succ_of_accept 14 15 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 15 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 188 (accept_3_2 13 15 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  15 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 188 (accept_3_2 10 15
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 188 (Polychromatic418967fa.accept_7_2_1_6_1_173
  9 15 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 188
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 15 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 188 (accept_3_2 7 15 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  188 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 15 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 188 (accept_3_2 4 15 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 15 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  15 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 188 (accept_3_2 1 15 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 188))))))))))))))) (allB_succ 14 188 (allA_succ_of_accept 13 14
  188 (accept_3_2 13 14 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 188 2 6 7 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 14 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 188 2 5 7 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 188 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 14 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 188 2 4 7 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 188 (accept_3_2 7 14 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 188 2 3 7 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 14 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 188 2 2 7 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 14
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 188 2 1 7 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 188 (accept_3_2 1 14
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 188)))))))))))))) (allB_succ 13 188 (allA_of_3_0 13 13 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 188 (allA_succ_of_accept 11 12 188
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 188 2 5 6 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 188 (Polychromatic418967fa.accept_21_9_12_20_1_10792 9 12 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 188 4 2 3 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 188 (accept_3_2 7 12 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 188 2 3 6 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 188 4 1 3 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 188 (Polychromatic418967fa.accept_15_3_12_8_1_738 3
  12 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 188 2 1 6 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 188 (accept_3_2 1 12
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 188)))))))))))) (allB_succ 11 188 (allA_succ_of_accept 10 11
  188 (accept_3_2 10 11 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 188
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 188 (Polychromatic418967fa.accept_13_8_11_6_1_1035 8 11 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 188 (accept_3_2 7 11 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 11 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  11 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 188 (accept_3_2 4 11 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 11 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 188 (accept_3_2 1 11 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  188))))))))))) (allB_succ 10 188 (allA_of_3_0 10 10 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 188
  (allA_succ_of_accept 8 9 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 9 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 188 (accept_3_2 7 9 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 9 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 188 (accept_3_2 4 9 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 9
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 188
  (Polychromatic418967fa.accept_13_2_9_6_1_501 2 9 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 188 (accept_3_2 1 9 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 188)))))))))
  (allB_succ 8 188 (allA_succ_of_accept 7 8 188 (accept_3_2 7 8 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 188 2 3 4 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 8 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 188 4 1 2 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 188 (Polychromatic418967fa.accept_16_3_8_12_1_2736 3 8 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 188 2 1 4 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 188 (accept_3_2 1 8 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 188)))))))) (allB_succ 7 188 (allA_of_3_0 7 7 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 188 (allA_succ_of_accept 5 6 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 6 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 188 2 2 3 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 188
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 6 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 188 2 1 3 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 188 (accept_3_2 1 6 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 188))))))
  (allB_succ 5 188 (allA_succ_of_accept 4 5 188 (accept_3_2 4 5 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 188 (accept_3_2 1 5 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 188))))) (allB_succ 4 188 (allA_of_3_0 4 4 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 188 (allA_succ_of_accept 2 3 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 3 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 188 (accept_3_2 1 3 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 188))) (allB_succ 2 188 (allA_succ_of_accept 1 2 188 (accept_3_2 1 2 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 188)) (allB_two
  188))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


