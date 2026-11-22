-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch216_Segment000
-- name    : Polychromatic418967fa_Branch216_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:33:29.588178+00:00
-- url     : https://prove2.me/theorems/fcdf60d8-5402-485d-b3e7-7a86581012ad
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

def Polychromatic418967fa.branch_216_segment_000 : allB 101 216 :=
  allB_succ 100 216 (allA_succ_of_accept 99 100 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 100 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 100 216 2 49 50 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 100 216
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 97 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 100 216 4 24 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 100 216 (accept_3_5 95 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 100 216 2 47 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 100 216 (Polychromatic418967fa.accept_15_3_10_6_1_632 93 100 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 100 216 4 23 25 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 100 216
  (Polychromatic418967fa.accept_15_1_10_6_1_631 91 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 100 216 2 45 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 100 216 (accept_3_5 89 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 100 216 4 22 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 100 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 100 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 100 216 2 43 50 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 100 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 85 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 100 216 4 21 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 100 216 (accept_3_5 83 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 100 216 2 41 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 100 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 100 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 100 216 4 20 25 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 100 216
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 79 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 100 216 2 39 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 100 216 (accept_3_5 77 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 100 216 4 19 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 100 216 (Polychromatic418967fa.accept_16_11_4_8_1_3435 75 100 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 100 216 2 37 50 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 100 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 73 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 100 216 4 18 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 100 216 (accept_3_5 71 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 100 216 2 35 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 100 216 (Polychromatic418967fa.accept_13_4_9_8_1_1736 69 100 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 100 216 4 17 25 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 100 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 100 216 2 33 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 100 216 (accept_3_5 65 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 100 216 4 16 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 100 216 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 100 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 100 216 2 31 50 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 100 216
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 61 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 100 216 4 15 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 100 216 (accept_3_5 59 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 100 216 2 29 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 100 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 100 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 100 216 4 14 25 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 100 216
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 55 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 100 216 2 27 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 100 216 (accept_3_5 53 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 100 216 4 13 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 100 216 (Polychromatic418967fa.accept_13_12_9_8_1_2595 51 100 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 216 2 25 50 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 216
  (Polychromatic418967fa.accept_15_4_10_6_1_2997 49 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 216 4 12 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 216 (accept_3_5 47 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 216 2 23 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 100 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 100 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 100 216 4 11 25 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 100 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 100 216 2 21 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 100 216 (accept_3_5 41 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 216 4 10 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 100 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 100 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 216 2 19 50 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 216
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 37 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 100 216 4 9 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 100 216 (accept_3_5 35 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  100 216 2 17 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 100 216 (Polychromatic418967fa.accept_13_7_9_8_1_188 33 100 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 216 4 8 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 31
  100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 216 2 15 50 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 216 (accept_3_5 29
  100 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 216 4 7 25 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 216
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 100 216 2 13 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 100 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 100 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 100 216 4 6 25 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 216 (accept_3_5 23 100 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 216 2 11 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 216 (Polychromatic418967fa.accept_16_5_4_8_1_1560
  21 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 216 4 5 25 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 216
  (Polychromatic418967fa.accept_15_4_10_6_1_2997 19 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 100 216 2 9 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 100 216 (accept_3_5 17 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 100 216 4 4 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 100 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 100 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 100 216 2 7 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 216 (Polychromatic418967fa.accept_16_13_4_8_1_4557
  13 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 216 4 3 25 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 216
  (accept_3_5 11 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 216 2 5 50 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 216
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 216 4 2 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 216 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 100 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 216 2 3 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 216 (accept_3_5 5 100 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100 216 4 1 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 100 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 100 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 216 2 1 50 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 100 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 100 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 99 216 (allA_succ_of_accept 98 99 216 (Polychromatic418967fa.accept_19_3_4_7_1_987 98 99 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 216
  (Polychromatic418967fa.accept_19_2_4_7_1_10048 97 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 216 3 32 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 95 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 216 (Polychromatic418967fa.accept_15_4_9_6_1_627 94 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 216 3 31 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 216
  (Polychromatic418967fa.accept_16_12_3_8_1_5729 92 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 216 (Polychromatic418967fa.accept_14_7_1_6_1_3514 91 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 216 9 10 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 89
  99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 216
  (Polychromatic418967fa.accept_19_12_4_7_1_4459 88 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 99 216 3 29 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 99 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 86 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 85 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 216 3 28 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 216
  (Polychromatic418967fa.accept_10_3_9_6_1_94 83 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 216 9 9 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 216 (Polychromatic418967fa.accept_21_17_15_6_1_3557 80 99
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 99 216 3 26 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 99 216 (Polychromatic418967fa.accept_14_7_1_6_1_3514 77 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 216 (Polychromatic418967fa.accept_15_1_9_6_1_1323 76 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 216 3 25 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 216
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 74 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 73 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 216 9 8 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 216 (Polychromatic418967fa.accept_15_11_9_6_1_1321 71 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 216
  (Polychromatic418967fa.accept_19_13_4_7_1_5878 70 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 99 216 3 23 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 216 (Polychromatic418967fa.accept_21_4_15_6_1_8327 67 99
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 216 3 22 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 216 (Polychromatic418967fa.accept_15_4_9_6_1_627 64 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 216 9 7 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 216 (Polychromatic418967fa.accept_17_11_14_12_1_2995 62 99
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 99 216 3 20 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 99 216 (Polychromatic418967fa.accept_15_14_9_6_1_5093 59 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 216 3 19 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 216
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 56 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 55 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 216 9 6 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 53 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 216
  (Polychromatic418967fa.accept_16_4_3_8_1_2486 52 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 99 216 3 17 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 99 216 (Polychromatic418967fa.accept_19_12_4_7_1_4459 50 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 216 (Polychromatic418967fa.accept_14_7_1_6_1_3514 49 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 216 3 16 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 216 (Polychromatic418967fa.accept_15_1_9_6_1_1323 46 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 216 9 5 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 216
  (Polychromatic418967fa.accept_10_3_9_6_1_94 43 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 99 216 3 14 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 99 216 (Polychromatic418967fa.accept_15_11_9_6_1_1321 41 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 216 3 13 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 216
  (Polychromatic418967fa.accept_21_17_15_6_1_3557 38 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 216 9 4 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 35 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 216
  (Polychromatic418967fa.accept_15_4_9_6_1_627 34 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 99 216 3 11 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 216 (Polychromatic418967fa.accept_17_15_14_12_1_1973 32 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 216 (Polychromatic418967fa.accept_15_1_9_6_1_1323 31 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 216 3 10 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 216
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 29 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 216 (Polychromatic418967fa.accept_16_12_3_8_1_5729 28 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 216 9 3 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 25 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 216 3 8 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 216 (Polychromatic418967fa.accept_19_3_4_7_1_987 22 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 216 3 7 33 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 216
  (Polychromatic418967fa.accept_16_4_3_8_1_2486 20 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 216 9 2 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 216 (Polychromatic418967fa.accept_20_17_19_16_1_6996 17 99
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 216 3 5 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 216 (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 216 3 4 33 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 216
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 216 (Polychromatic418967fa.accept_20_10_19_16_1_8521 10 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 216 9 1 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 216 (Polychromatic418967fa.accept_21_8_15_6_1_8247 8 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 216
  (Polychromatic418967fa.accept_14_7_1_6_1_3514 7 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 216 3 2 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 216 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 99 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 216 3 1 33 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 99 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 216 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 99 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99
  216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  216 (allA_succ_of_accept 97 98 216 (accept_3_4 97 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96
  98 216 2 48 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 216 (Polychromatic418967fa.accept_20_15_18_16_1_5441 95 98 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 216 2 47 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 93
  98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 216 2 46 49 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 98 216 (accept_3_4 91
  98 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 98 216 2 45 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 216
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 89 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 216 2 44 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 98 216 (Polychromatic418967fa.accept_13_9_7_8_1_1122 87 98 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 216 2 43 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 216 (accept_3_4 85 98 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 216 2 42 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 83
  98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 216 2 41 49 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 216
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 81 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 216 2 40 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 98 216 (accept_3_4 79 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 216 2 39 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 98 216 (Polychromatic418967fa.accept_13_12_7_8_1_1104 77 98 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 98 216 2 38 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 98 216
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 75 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 98 216 2 37 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 98 216 (accept_3_4 73 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 98 216 2 36 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 98 216 (Polychromatic418967fa.accept_19_14_3_7_1_7248 71 98 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 216 2 35 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 216
  (Polychromatic418967fa.accept_11_3_10_7_1_129 69 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 98 216 2 34 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 98 216 (accept_3_4 67 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 98 216 2 33 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 98 216 (Polychromatic418967fa.accept_20_5_18_16_1_1558 65 98 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 216 2 32 49 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 98 216 2 31 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 98 216 (accept_3_4 61 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 98 216 2 30 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 98 216 (Polychromatic418967fa.accept_15_14_8_6_1_2133 59 98 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 216 2 29 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 216
  (Polychromatic418967fa.accept_25_7_23_16_1_12769 57 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 98 216 2 28 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 98 216 (accept_3_4 55 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 98 216 2 27 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 98 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 53 98 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 216 2 26 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 216
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 51 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 216 2 25 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 98 216 (accept_3_4 49 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 98 216 2 24 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 98 216 (Polychromatic418967fa.accept_11_3_10_7_1_129 47 98 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 216 2 23 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 216
  (Polychromatic418967fa.accept_17_11_13_12_1_1968 45 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 98 216 2 22 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 98 216 (accept_3_4 43 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 216 2 21 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 98 216 (Polychromatic418967fa.accept_13_2_7_8_1_4221 41 98 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 216 2 20 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 216
  (Polychromatic418967fa.accept_21_18_14_6_1_8278 39 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 216 2 19 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 98 216 (accept_3_4 37 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 98 216 2 18 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 98 216 (Polychromatic418967fa.accept_13_9_7_8_1_1122 35 98 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 216 2 17 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 216 2 16 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 216 (accept_3_4 31 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 216 2 15 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 216 (Polychromatic418967fa.accept_13_3_7_8_1_4192 29 98 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 216 2 14 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 216
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 216 2 13 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 98 216 (accept_3_4 25 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 98 216 2 12 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 98 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 98 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 216 2 11 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 216
  (Polychromatic418967fa.accept_20_1_18_16_1_12711 21 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 98 216 2 10 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 98 216 (accept_3_4 19 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 216 2 9 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 216 (Polychromatic418967fa.accept_15_2_8_6_1_1340 17 98 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 216 2 8 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 216 (Polychromatic418967fa.accept_13_2_7_8_1_4221
  15 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 216 2 7 49 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 216 (accept_3_4 13
  98 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 216 2 6 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 98 216
  (Polychromatic418967fa.accept_17_11_13_12_1_1968 11 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 216 2 5 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 98 216 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 98 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 216 2 4 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 216 (accept_3_4 7 98 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 216 2 3 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 98 216 (Polychromatic418967fa.accept_19_5_3_7_1_10042 5 98 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 216 2 2 49 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 216 2 1 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 216 (accept_3_4 1 98 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  216 (allA_succ_of_accept 96 97 216 (Polychromatic418967fa.accept_14_12_13_6_1_1140 96 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 216 (accept_3_5 95 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 97 216 (Polychromatic418967fa.accept_25_19_22_16_1_12768 94 97 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 93 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 97 216 (accept_3_5 92 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  97 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 91 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 97 216 (Polychromatic418967fa.accept_11_2_9_7_1_124 90 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 216 (accept_3_5 89 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 97 216 (Polychromatic418967fa.accept_15_13_7_6_1_682 88 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 216
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 87 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 97 216 (accept_3_5 86 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  97 216 (Polychromatic418967fa.accept_19_9_2_7_1_3149 85 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 97 216 (Polychromatic418967fa.accept_16_4_1_8_1_835 84 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 216 (accept_3_5 83 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 97 216 (Polychromatic418967fa.accept_11_5_9_7_1_411 82 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 81 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 97 216 (accept_3_5 80 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  97 216 (Polychromatic418967fa.accept_11_2_9_7_1_124 79 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 97 216 (Polychromatic418967fa.accept_21_15_13_6_1_6659 78 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 216 (accept_3_5 77 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 97 216 (Polychromatic418967fa.accept_13_11_6_8_1_1121 76 97
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 216
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 75 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 97 216 (accept_3_5 74 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  97 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 73 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 97 216 (Polychromatic418967fa.accept_15_12_7_6_1_4013 72 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 216 (accept_3_5 71 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 216 (Polychromatic418967fa.accept_19_13_2_7_1_8738 70 97
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 216
  (Polychromatic418967fa.accept_22_3_9_18_1_12767 69 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 216 (accept_3_5 68 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 216 (Polychromatic418967fa.accept_13_2_6_8_1_1092 67 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 216 (Polychromatic418967fa.accept_13_1_6_8_1_208 66 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 216 (accept_3_5 65 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 216 (Polychromatic418967fa.accept_22_20_9_18_1_8087 64 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 63 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 216 (accept_3_5 62 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 61 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 216 (Polychromatic418967fa.accept_11_5_9_7_1_411 60 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 216 (accept_3_5 59 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 216 (Polychromatic418967fa.accept_15_13_7_6_1_682 58 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 216
  (Polychromatic418967fa.accept_11_2_9_7_1_124 57 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 216 (accept_3_5 56 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 216 (Polychromatic418967fa.accept_16_7_1_8_1_5796 55 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 216 (Polychromatic418967fa.accept_13_2_6_8_1_1092 54 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 216 (accept_3_5 53 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 216 (Polychromatic418967fa.accept_16_4_1_8_1_835 52 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 51 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 216 (accept_3_5 50 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 216 (Polychromatic418967fa.accept_11_5_9_7_1_411 49 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 216 (Polychromatic418967fa.accept_25_23_22_16_1_12766 48 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 216 (accept_3_5 47 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 216 (Polychromatic418967fa.accept_11_2_9_7_1_124 46 97 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 216
  (Polychromatic418967fa.accept_21_3_13_6_1_11322 45 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 216 (accept_3_5 44 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 43 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 216 (Polychromatic418967fa.accept_15_12_7_6_1_4013 42 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 216 (accept_3_5 41 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 216 (Polychromatic418967fa.accept_13_1_6_8_1_208 40 97 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 216
  (Polychromatic418967fa.accept_16_7_1_8_1_5796 39 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 216 (accept_3_5 38 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 216 (Polychromatic418967fa.accept_13_11_6_8_1_1121 37 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 216 (Polychromatic418967fa.accept_16_4_1_8_1_835 36 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 216 (accept_3_5 35 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 216 (Polychromatic418967fa.accept_25_9_22_16_1_12765 34 97 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 33 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 216 (accept_3_5 32 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 31 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 216 (Polychromatic418967fa.accept_21_9_13_6_1_2285 30 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 216 (accept_3_5 29 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 216 (Polychromatic418967fa.accept_13_2_6_8_1_1092 28 97 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 216
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 216 (accept_3_5 26 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 216 (Polychromatic418967fa.accept_16_9_1_8_1_5766 25 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 216 (Polychromatic418967fa.accept_11_2_9_7_1_124 24 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 216 (accept_3_5 23 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 216 (Polychromatic418967fa.accept_31_22_4_30_1_12764 22 97 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 21 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 216 (accept_3_5 20 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 216 (Polychromatic418967fa.accept_14_5_13_6_1_3574 19 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 216 (Polychromatic418967fa.accept_21_18_13_6_1_12763 18 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 216 (accept_3_5 17 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 216 (Polychromatic418967fa.accept_11_5_9_7_1_411 16 97 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 216
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 216 (accept_3_5 14 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 216 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 216 (accept_3_5 11 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 216 (Polychromatic418967fa.accept_22_10_9_18_1_12762 10 97
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 216
  (Polychromatic418967fa.accept_16_9_1_8_1_5766 9 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 216 (accept_3_5 8 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  216 (Polychromatic418967fa.accept_14_7_13_6_1_1177 7 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 216 (Polychromatic418967fa.accept_20_6_17_16_1_8470 6 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 216 (accept_3_5 5 97 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 216 (Polychromatic418967fa.accept_16_4_1_8_1_835 4 97 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 3 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 216 (accept_3_5 2 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  216 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 97 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 96 216 (allA_succ_of_accept 95 96 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 95 96 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 96 216 2 47 48 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 96 216 3 31 32 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 96 216 4 23 24 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 216
  (Polychromatic418967fa.accept_17_6_11_12_1_4107 91 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 96 216 6 15 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 96 216 (Polychromatic418967fa.accept_19_13_1_7_1_5906 89 96 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 216 8 11 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 96 216 3 29 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 96 216 2 43 48 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 96 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 85 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 216 12 7 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 216 (Polychromatic418967fa.accept_14_13_12_6_1_2735 83 96 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 216 2 41 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 96 216 3 27 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 96 216 8 10 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 79
  96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 216 6 13 16 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 216
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 77 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 96 216 4 19 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 75 96 216 3 25 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 96 216 2 37 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 96 216 (Polychromatic418967fa.accept_21_10_12_6_1_5124 73 96 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 216 24 3 4 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 96 216 2 35 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 96 216 3 23 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 68 96 216 4 17 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 96 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 96 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 216 6 11 16 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 216
  (Polychromatic418967fa.accept_17_14_11_12_1_4109 65 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 96 216 8 8 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 96 216 3 21 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 62 96 216 2 31 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 96 216 (Polychromatic418967fa.accept_19_4_1_7_1_4438 61 96 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 216 12 5 8 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 216
  (Polychromatic418967fa.accept_11_4_8_7_1_819 59 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 96 216 2 29 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 96 216 3 19 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 56 96 216 8 7 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 96 216 (Polychromatic418967fa.accept_13_3_5_8_1_1099 55 96 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 216 6 9 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 53
  96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 216 4 13 24 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 96 216 3 17 32 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 96 216 2 25 48 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 216
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 49 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 216 24 2 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 216 (Polychromatic418967fa.accept_17_13_11_12_1_4131 47 96 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 216 2 23 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 96 216 3 15 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 96 216 4 11 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 43
  96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 216 6 7 16 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 216
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 41 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 96 216 8 5 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 96 216 3 13 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 96 216 2 19 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 96 216 (Polychromatic418967fa.accept_11_4_8_7_1_819 37 96 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 216 12 3 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 216 (Polychromatic418967fa.accept_21_14_12_6_1_8222
  35 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 216 2 17 48 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 96 216 3 11 32 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 96 216 8 4 12 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 216
  (Polychromatic418967fa.accept_17_14_11_12_1_4109 31 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 96 216 6 5 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 96 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 96 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 216 4 7 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 96 216 3 9 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 96 216 2 13 48 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 216 24 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 216 (Polychromatic418967fa.accept_13_10_5_8_1_2555 23 96 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 216 2 11 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 96 216 3 7 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 96 216 4 5 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 216 (Polychromatic418967fa.accept_21_19_12_6_1_6689
  19 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 216 6 3 16 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 216
  (Polychromatic418967fa.accept_21_17_12_6_1_12761 17 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 216 8 2 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 96 216 3 5 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 96 216 2 7 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 96 216 (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 96 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 216 12 1 8 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 96 216 2 5 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 96 216 3 3 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 96 216 8 1 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 216 (Polychromatic418967fa.accept_21_7_12_6_1_3624 7 96 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 216 6 1 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 216 (Polychromatic418967fa.accept_21_5_12_6_1_11321 5 96 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 216 4 1 24 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 96 216 3 1 32 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 96 216 2 1 48 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 96 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 95 216 (allA_succ_of_accept 94 95 216 (accept_3_4 94 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 95 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 95 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 95 216 (Polychromatic418967fa.accept_16_12_15_8_1_4586 92 95
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 216 (accept_3_4 91 95 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 216 (Polychromatic418967fa.accept_13_12_4_8_1_1120
  90 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 89 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 216 (accept_3_4 88 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 86 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 216 (accept_3_4 85 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 84 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 216
  (Polychromatic418967fa.accept_21_20_11_6_1_8306 83 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 216 (accept_3_4 82 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 81 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 216 (accept_3_4 79 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 216 (Polychromatic418967fa.accept_15_3_5_6_1_4005 78 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 216
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 77 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 216 (accept_3_4 76 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 74 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 216 (accept_3_4 73 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 71 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 216 (accept_3_4 70 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 69 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 216 (accept_3_4 67 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 216 (accept_3_4 64 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 216 (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 216 (Polychromatic418967fa.accept_13_10_4_8_1_2570 62 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 216 (accept_3_4 61 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 216 (Polychromatic418967fa.accept_16_12_15_8_1_4586 60 95
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 216 (accept_3_4 58 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 216 (Polychromatic418967fa.accept_15_12_5_6_1_2148 57 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 216 (Polychromatic418967fa.accept_15_11_5_6_1_669 56 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 216 (accept_3_4 55 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 216
  (Polychromatic418967fa.accept_17_2_10_12_1_7915 53 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 216 (accept_3_4 52 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 216 (Polychromatic418967fa.accept_13_11_4_8_1_1098 50 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 216 (accept_3_4 49 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 216 (Polychromatic418967fa.accept_13_9_4_8_1_1752 48 95 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 216 (accept_3_4 46 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 216 (accept_3_4 43 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 216 (Polychromatic418967fa.accept_15_12_5_6_1_2148 42 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 41 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 216 (accept_3_4 40 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 216 (accept_3_4 37 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 216 (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 216
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 35 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 216 (accept_3_4 34 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 216 (Polychromatic418967fa.accept_25_7_20_16_1_3728 32 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 216 (accept_3_4 31 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 95 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 216
  (Polychromatic418967fa.accept_10_9_5_6_1_691 29 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 216 (accept_3_4 28 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 216 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 216 (accept_3_4 25 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 216 (accept_3_4 22 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 216 (Polychromatic418967fa.accept_16_4_15_8_1_2413 20 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 216 (accept_3_4 19 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 216 (Polychromatic418967fa.accept_15_3_5_6_1_4005 18 95 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 216 (accept_3_4 16 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 216 (Polychromatic418967fa.accept_21_15_11_6_1_5121 15 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 216 (accept_3_4 13 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 11 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 216 (accept_3_4 10 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 216 (Polychromatic418967fa.accept_17_8_10_12_1_5335 8 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 216 (accept_3_4 7 95 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 216 (Polychromatic418967fa.accept_17_6_10_12_1_4129 6 95 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 216 (accept_3_4 4 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  216 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 95 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 95 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 216 (accept_3_4 1 95 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 216
  (allA_succ_of_accept 93 94 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 94 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 94 216 2 46 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 94 216
  (Polychromatic418967fa.accept_19_15_18_7_1_10018 91 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 94 216 2 45 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 94 216 (accept_3_5 89 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 94 216 2 44 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 94 216 (Polychromatic418967fa.accept_13_9_3_8_1_573 87 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 94 216 2 43 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 94 216
  (Polychromatic418967fa.accept_10_5_4_6_1_319 85 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 94 216 2 42 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 94 216 (accept_3_5 83 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 94 216 2 41 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 94 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 94 216 2 40 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 94 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 79 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 94 216 2 39 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 94 216 (accept_3_5 77 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 94 216 2 38 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 94 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 75 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 94 216 2 37 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 94 216
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 73 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 94 216 2 36 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 94 216 (accept_3_5 71 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 94 216 2 35 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 94 216 (Polychromatic418967fa.accept_15_9_4_6_1_3075 69 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 94 216 2 34 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 94 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 67 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 94 216 2 33 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 94 216 (accept_3_5 65 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 94 216 2 32 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 94 216 (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 94 216 2 31 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 94 216
  (Polychromatic418967fa.accept_13_9_3_8_1_573 61 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 94 216 2 30 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 94 216 (accept_3_5 59 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 94 216 2 29 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 94 216 (Polychromatic418967fa.accept_13_5_3_8_1_1117 57 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 94 216 2 28 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 94 216
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 94 216 2 27 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 94 216 (accept_3_5 53 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 94 216 2 26 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 94 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 216 2 25 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 216
  (Polychromatic418967fa.accept_19_11_18_7_1_4466 49 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 216 2 24 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 94 216 (accept_3_5 47 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 94 216 2 23 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 94 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 216 2 22 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 216
  (Polychromatic418967fa.accept_15_13_4_6_1_3046 43 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 216 2 21 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 94 216 (accept_3_5 41 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 94 216 2 20 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 94 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 94 216 2 19 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 216 2 18 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 94 216 (accept_3_5 35 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 94 216 2 17 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 94 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 33 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 216 2 16 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 216
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 31 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 216 2 15 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 94 216 (accept_3_5 29 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 94 216 2 14 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 94 216 (Polychromatic418967fa.accept_19_8_18_7_1_3143 27 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 216 2 13 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 216 2 12 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 94 216 (accept_3_5 23 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 94 216 2 11 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 94 216 (Polychromatic418967fa.accept_17_4_9_12_1_9167 21 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 216 2 10 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 216
  (Polychromatic418967fa.accept_26_19_16_8_1_11001 19 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 94 216 2 9 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 94 216 (accept_3_5 17 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 94 216 2 8 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 94 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 94 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 216 2 7 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 216 (Polychromatic418967fa.accept_15_13_4_6_1_3046
  13 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 216 2 6 47 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 216 (accept_3_5 11
  94 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 216 2 5 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 216 2 4 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 94 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 216 2 3 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 216 (accept_3_5 5 94 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 216 2 2 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 216 (Polychromatic418967fa.accept_14_3_10_6_1_1136 3 94 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 216 2 1 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 1
  94 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 216
  (allA_succ_of_accept 92 93 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 92 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 216 (Polychromatic418967fa.accept_15_1_3_6_1_621 91 93 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 216 3 30 31 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 216
  (Polychromatic418967fa.accept_10_9_3_6_1_686 89 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 88 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 216 3 29 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 216 (Polychromatic418967fa.accept_11_9_5_7_1_815 86
  93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 85 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 216 3 28 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 216 (Polychromatic418967fa.accept_16_3_13_8_1_1594 83 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 216 (Polychromatic418967fa.accept_22_16_5_18_1_12760 82 93
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 216 3 27 31 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 79 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 216 3 26 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 77
  93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 216
  (Polychromatic418967fa.accept_15_1_3_6_1_621 76 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 216 3 25 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 74 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 93 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 216 3 24 31 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 216 (Polychromatic418967fa.accept_15_10_3_6_1_3042 70 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 216 3 23 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 68
  93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 216 3 22 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 216 (Polychromatic418967fa.accept_15_5_3_6_1_2128 65 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 93 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 216 3 21 31 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 216
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 62 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 216 (Polychromatic418967fa.accept_15_1_3_6_1_621 61 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 216 3 20 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 59
  93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 216
  (Polychromatic418967fa.accept_10_8_3_6_1_685 58 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 216 3 19 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 216 (Polychromatic418967fa.accept_15_11_3_6_1_1306 56 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 216 (Polychromatic418967fa.accept_15_10_3_6_1_3042 55 93
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 216 3 18 31 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 216 3 17 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 50
  93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 216
  (Polychromatic418967fa.accept_10_9_3_6_1_686 49 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 216 3 16 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 47 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 93 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 216 3 15 31 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 216
  (Polychromatic418967fa.accept_16_12_13_8_1_2409 44 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 216 3 14 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 216 (Polychromatic418967fa.accept_15_11_3_6_1_1306
  41 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 216
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 40 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 93 216 3 13 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 37 93 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 216 3 12 31 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 216
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 35 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 216 (Polychromatic418967fa.accept_19_15_17_7_1_8734 34 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 216 3 11 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 32
  93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 93 216 3 10 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 93 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 93 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 216 3 9 31 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 216
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 216 3 8 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 216 (Polychromatic418967fa.accept_13_10_2_8_1_2603 23 93 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 216 3 7 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 216 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 93 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 216 3 6 31 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 216 (Polychromatic418967fa.accept_15_1_3_6_1_621 16 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 216 3 5 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 216 (Polychromatic418967fa.accept_21_14_9_6_1_11289 14 93
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 216
  (Polychromatic418967fa.accept_19_13_17_7_1_12726 13 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 93 216 3 4 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 93 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 93 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 10
  93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 216 3 3 31 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 216 3 2 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 216 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 93 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 93 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 216 3 1 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 216 (Polychromatic418967fa.accept_19_2_17_7_1_8735 2 93 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 93 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 216
  (allA_succ_of_accept 91 92 216 (accept_3_4 91 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  216 2 45 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 216 4 22 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 216 (Polychromatic418967fa.accept_13_9_1_8_1_1742 87 92 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 216 2 43 46 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 216 (accept_3_4 85 92 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 216 4 21 23 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 216
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 83 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 216 2 41 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 92 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 216 4 20 23 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 216 (accept_3_4 79 92 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 216 2 39 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 216 (Polychromatic418967fa.accept_13_12_1_8_1_1779
  77 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 216 4 19 23 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 216 2 37 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 92 216 (accept_3_4 73 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 92 216 4 18 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 92 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 71 92 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 216 2 35 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 216 (Polychromatic418967fa.accept_11_3_4_7_1_114 69
  92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 216 4 17 23 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 216 (accept_3_4 67
  92 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 216 2 33 46 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 216 4 16 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 216 (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 92 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 216 2 31 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 216 (accept_3_4 61 92 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 216 4 15 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 216 (Polychromatic418967fa.accept_13_7_1_8_1_1778 59 92 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 216 2 29 46 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 216
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 57 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 216 4 14 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 92 216 (accept_3_4 55 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92
  216 2 27 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 92 216 (Polychromatic418967fa.accept_15_8_2_6_1_2125 53 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 92 216 4 13 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 92 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 216 2 25 46 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 216 (accept_3_4 49 92 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 216 4 12 23 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 216 2 23 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 92 216 (Polychromatic418967fa.accept_13_6_1_8_1_1116 45 92 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 216 4 11 23 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 216 (accept_3_4 43 92 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 216 2 21 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 41
  92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 216 4 10 23 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 216
  (Polychromatic418967fa.accept_16_7_12_8_1_2450 39 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 216 2 19 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 92 216 (accept_3_4 37 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 92 216 4 9 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 92 216 (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 92 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 216 2 17 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 33
  92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 216 4 8 23 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 216 (accept_3_4 31
  92 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 216 2 15 46 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 216
  (Polychromatic418967fa.accept_16_13_12_8_1_2451 29 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 92 216 4 7 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 92 216 (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 92 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 216 2 13 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 216 (accept_3_4 25 92 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 216 4 6 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 92 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 92 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 216 2 11 46 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 216 4 5 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 216 (accept_3_4 19 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  216 2 9 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 216 (Polychromatic418967fa.accept_16_1_12_8_1_2405 17 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 216 4 4 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 216 (Polychromatic418967fa.accept_16_15_12_8_1_4585 15 92 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 216 2 7 46 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 216 (accept_3_4 13 92 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 216 4 3 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 11
  92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 216 2 5 46 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 216 4 2 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 216 (accept_3_4 7 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 216
  2 3 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  216 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 92 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 216 4 1 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 216 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 92 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 216 2 1 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 216 (accept_3_4 1 92 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 216
  (allA_succ_of_accept 90 91 216 (Polychromatic418967fa.accept_19_14_15_7_1_7205 90 91 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 216 (accept_3_5 89 91 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 216 (Polychromatic418967fa.accept_19_12_15_7_1_11432 88 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 216
  (Polychromatic418967fa.accept_10_7_1_6_1_673 87 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 91 216 (accept_3_5 86 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  91 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 85 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 91 216 (Polychromatic418967fa.accept_15_9_1_6_1_657 84 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 216 (accept_3_5 83 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 91 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 82 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 216
  (Polychromatic418967fa.accept_11_4_3_7_1_828 81 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 91 216 (accept_3_5 80 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  91 216 (Polychromatic418967fa.accept_17_11_6_12_1_5348 79 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 91 216 (Polychromatic418967fa.accept_14_8_7_6_1_1159 78 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 216 (accept_3_5 77 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 91 216 (Polychromatic418967fa.accept_11_10_3_7_1_2564 76 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 216
  (Polychromatic418967fa.accept_10_5_1_6_1_672 75 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 91 216 (accept_3_5 74 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  91 216 (Polychromatic418967fa.accept_22_7_3_18_1_12759 73 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 216 (accept_3_5 71 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 216 (Polychromatic418967fa.accept_11_4_3_7_1_828 70 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 216
  (Polychromatic418967fa.accept_14_13_7_6_1_3525 69 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 216 (accept_3_5 68 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 67 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 216 (Polychromatic418967fa.accept_20_6_11_16_1_3992 66 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 216 (accept_3_5 65 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 216 (Polychromatic418967fa.accept_14_8_7_6_1_1159 64 91 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 216
  (Polychromatic418967fa.accept_15_3_1_6_1_206 63 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 216 (accept_3_5 62 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 216 (Polychromatic418967fa.accept_16_13_11_8_1_2449 61 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 216 (Polychromatic418967fa.accept_16_12_11_8_1_832 60 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 216 (accept_3_5 59 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 216 (Polychromatic418967fa.accept_20_18_11_16_1_6973 58 91
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 216
  (Polychromatic418967fa.accept_10_7_1_6_1_673 57 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 216 (accept_3_5 56 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 55 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 216 (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 216 (accept_3_5 53 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 91 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 216
  (Polychromatic418967fa.accept_16_3_11_8_1_830 51 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 216 (accept_3_5 50 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 216 (Polychromatic418967fa.accept_19_11_15_7_1_3177 49 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 216 (Polychromatic418967fa.accept_11_4_3_7_1_828 48 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 216 (accept_3_5 47 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 216 (Polychromatic418967fa.accept_19_8_15_7_1_323 46 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 216
  (Polychromatic418967fa.accept_10_5_1_6_1_672 45 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 216 (accept_3_5 44 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 216 (Polychromatic418967fa.accept_11_10_3_7_1_2564 43 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 216 (accept_3_5 41 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 216 (Polychromatic418967fa.accept_15_10_1_6_1_3033 40 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 216
  (Polychromatic418967fa.accept_15_9_1_6_1_657 39 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 216 (accept_3_5 38 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 216 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 216 (accept_3_5 35 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 216 (Polychromatic418967fa.accept_21_13_7_6_1_3656 34 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 216
  (Polychromatic418967fa.accept_15_3_1_6_1_206 33 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 216 (accept_3_5 32 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 216 (Polychromatic418967fa.accept_19_12_15_7_1_11432 31 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 216 (Polychromatic418967fa.accept_19_11_15_7_1_3177 30 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 216 (accept_3_5 29 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 216 (Polychromatic418967fa.accept_16_12_11_8_1_832 28 91
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 216
  (Polychromatic418967fa.accept_10_7_1_6_1_673 27 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 216 (accept_3_5 26 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 216 (Polychromatic418967fa.accept_15_9_1_6_1_657 24 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 216 (accept_3_5 23 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 216
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 216 (accept_3_5 20 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 216 (Polychromatic418967fa.accept_16_3_11_8_1_830 19 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 216 (Polychromatic418967fa.accept_15_3_1_6_1_206 18 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 216 (accept_3_5 17 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 216 (Polychromatic418967fa.accept_21_16_7_6_1_6687 16 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 216
  (Polychromatic418967fa.accept_10_5_1_6_1_672 15 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 216 (accept_3_5 14 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 216 (Polychromatic418967fa.accept_14_13_7_6_1_3525 13 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 216 (accept_3_5 11 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 216 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 91 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 216
  (Polychromatic418967fa.accept_15_9_1_6_1_657 9 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 216 (accept_3_5 8 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  216 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 216 (Polychromatic418967fa.accept_20_6_11_16_1_3992 6 91 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 216 (accept_3_5 5 91 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 216 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 91 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 216 (Polychromatic418967fa.accept_15_3_1_6_1_206 3
  91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 216 (accept_3_5 2 91 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 216 (Polychromatic418967fa.accept_14_1_7_6_1_3604 1
  91 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 216
  (allA_succ_of_accept 89 90 216 (Polychromatic418967fa.accept_20_9_10_16_1_8454 89 90 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 90 216 2 44 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 90 216 3 29 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 90 216 2 43 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 216
  (Polychromatic418967fa.accept_13_7_12_8_1_199 85 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 90 216 6 14 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 90 216 (Polychromatic418967fa.accept_13_5_12_8_1_198 83 90 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 216 2 41 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 90 216 9 9 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 90 216 2 40 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 216
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 79 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 216 6 13 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 90 216 (Polychromatic418967fa.accept_17_9_5_12_1_6606 77 90 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 216 2 38 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 90 216 3 25 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 90 216 2 37 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 216
  (Polychromatic418967fa.accept_22_7_2_18_1_12758 73 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 216 18 4 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 216 (Polychromatic418967fa.accept_22_5_2_18_1_4720 71 90 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 216 2 35 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 90 216 3 23 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 90 216 2 34 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 216
  (Polychromatic418967fa.accept_19_10_14_7_1_11440 67 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 90 216 6 11 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 90 216 (Polychromatic418967fa.accept_19_8_14_7_1_10047 65 90 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 216 2 32 45 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 90 216 9 7 10 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 90 216 2 31 45 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 216
  (Polychromatic418967fa.accept_13_9_12_8_1_570 61 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 216 6 10 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 90 216 (Polychromatic418967fa.accept_13_7_12_8_1_199 59 90 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 216 2 29 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 90 216 3 19 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 90 216 2 28 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 216
  (Polychromatic418967fa.accept_20_15_10_16_1_8506 55 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 90 216 18 3 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 90 216 (Polychromatic418967fa.accept_11_9_2_7_1_1298 53 90 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 216 2 26 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 90 216 3 17 30 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 90 216 2 25 45 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 216
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 49 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 216 6 8 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 90 216 (Polychromatic418967fa.accept_25_22_15_16_1_7286 47 90 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 216 2 23 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 216 9 5 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 90 216 2 22 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 216
  (Polychromatic418967fa.accept_13_4_12_8_1_197 43 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 216 6 7 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 90 216 (Polychromatic418967fa.accept_17_7_5_12_1_1997 41 90 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 216 2 20 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 90 216 3 13 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 90 216 2 19 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 216
  (Polychromatic418967fa.accept_19_18_14_7_1_5864 37 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 216 18 2 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 216 (Polychromatic418967fa.accept_13_9_12_8_1_570 35 90 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 216 2 17 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 90 216 3 11 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 90 216 2 16 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 216
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 31 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 216 6 5 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 90 216 (Polychromatic418967fa.accept_19_10_14_7_1_11440 29 90 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 216 2 14 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 90 216 9 3 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 90 216 2 13 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 216
  (Polychromatic418967fa.accept_17_8_5_12_1_7925 25 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 216 6 4 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 90 216 (Polychromatic418967fa.accept_13_10_12_8_1_2550 23 90 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 216 2 11 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 90 216 3 7 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 90 216 2 10 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 216
  (Polychromatic418967fa.accept_20_19_10_16_1_7001 19 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 90 216 18 1 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 90 216 (Polychromatic418967fa.accept_13_4_12_8_1_197 17 90 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 216 2 8 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 216 3 5 30 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 216 2 7 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 216
  (Polychromatic418967fa.accept_22_13_2_18_1_4747 13 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 90 216 6 2 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 90 216 (Polychromatic418967fa.accept_19_11_14_7_1_4473 11 90 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 216 2 5 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 216 9 1 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 90 216 2 4 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 216 (Polychromatic418967fa.accept_13_7_12_8_1_199 7
  90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 216 6 1 15 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 216
  (Polychromatic418967fa.accept_13_5_12_8_1_198 5 90 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 90 216 2 2 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 90 216 3 1 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 90 216 2 1 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 216 (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 90 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 216
  (allA_succ_of_accept 88 89 216 (accept_3_4 88 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 87 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 216 (Polychromatic418967fa.accept_22_20_1_18_1_12757 86 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 216 (accept_3_4 85 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 216 (Polychromatic418967fa.accept_13_6_11_8_1_1111 84 89
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 216
  (Polychromatic418967fa.accept_10_3_9_6_1_94 83 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 216 (accept_3_4 82 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 216 (Polychromatic418967fa.accept_15_5_14_6_1_5120 80 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 216 (accept_3_4 79 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 89 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 216
  (Polychromatic418967fa.accept_17_9_4_12_1_2958 77 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 216 (accept_3_4 76 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 75 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 89 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 216 (accept_3_4 73 89 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 216 (Polychromatic418967fa.accept_11_6_1_7_1_1315 72 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 216 (accept_3_4 70 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 216 (Polychromatic418967fa.accept_13_4_11_8_1_1768 69 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 216 (Polychromatic418967fa.accept_13_3_11_8_1_1094 68 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 216 (accept_3_4 67 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 216 (Polychromatic418967fa.accept_13_1_11_8_1_2562 66 89
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 65 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 216 (accept_3_4 64 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 216 (Polychromatic418967fa.accept_13_10_11_8_1_1770 62 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 216 (accept_3_4 61 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 89 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 216
  (Polychromatic418967fa.accept_17_8_4_12_1_1994 59 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 216 (accept_3_4 58 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 216 (Polychromatic418967fa.accept_13_4_11_8_1_1768 56 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 216 (accept_3_4 55 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 216 (Polychromatic418967fa.accept_15_9_14_6_1_3004 54 89
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 216 (accept_3_4 52 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 216 (Polychromatic418967fa.accept_22_7_1_18_1_12756 51 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 89 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 216 (accept_3_4 49 89 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 48 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 216
  (Polychromatic418967fa.accept_16_15_9_8_1_2440 47 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 216 (accept_3_4 46 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 216 (Polychromatic418967fa.accept_16_12_9_8_1_2508 44 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 216 (accept_3_4 43 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 216 (Polychromatic418967fa.accept_13_3_11_8_1_1094 42 89
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 216
  (Polychromatic418967fa.accept_14_13_5_6_1_2747 41 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 216 (accept_3_4 40 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 216 (Polychromatic418967fa.accept_15_8_14_6_1_3003 38 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 216 (accept_3_4 37 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 89 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 35 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 216 (accept_3_4 34 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 89 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 216 (accept_3_4 31 89 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 216 (Polychromatic418967fa.accept_13_4_11_8_1_1768 30 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 216 (accept_3_4 28 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 216 (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 216 (Polychromatic418967fa.accept_17_9_4_12_1_2958 26 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 216 (accept_3_4 25 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 216 (Polychromatic418967fa.accept_15_9_14_6_1_3004 24 89
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 216
  (Polychromatic418967fa.accept_10_3_9_6_1_94 23 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 216 (accept_3_4 22 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 216 (Polychromatic418967fa.accept_19_2_13_7_1_7211 21 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 216 (Polychromatic418967fa.accept_15_5_14_6_1_5120 20 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 216 (accept_3_4 19 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 89 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 216
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 216 (accept_3_4 16 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 216 (Polychromatic418967fa.accept_13_1_11_8_1_2562 14 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 216 (accept_3_4 13 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 216 (Polychromatic418967fa.accept_16_12_9_8_1_2508 12 89
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 216 (accept_3_4 10 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 89 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 216 (accept_3_4 7 89 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 216 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 89 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 5 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 216 (accept_3_4 4 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  216 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 89 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 216 (Polychromatic418967fa.accept_17_2_4_12_1_6587 2 89 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 216 (accept_3_4 1 89 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 216 (allA_succ_of_accept 87 88 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 88 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 88 216 2 43 44 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 88 216
  (Polychromatic418967fa.accept_13_7_10_8_1_567 85 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 88 216 4 21 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 88 216 (accept_3_5 83 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 88
  216 2 41 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  81 88 216 (Polychromatic418967fa.accept_19_5_12_7_1_4416 81 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 88 216 8 10 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 88 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 88 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 88 216 2 39 44 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 88 216 (accept_3_5 77 88 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 88 216 4 19 22 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 88 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 88 216 2 37 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 88 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 88 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 88 216 8 9 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 88 216 (accept_3_5 71 88 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 88 216 2 35 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 88 216 (Polychromatic418967fa.accept_13_4_10_8_1_1817 69 88 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 88 216 4 17 22 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 88 216
  (Polychromatic418967fa.accept_13_2_10_8_1_1126 67 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 88 216 2 33 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 88 216 (accept_3_5 65 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 88 216 8 8 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 88 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 88 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 88 216 2 31 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 88 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 61
  88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 88 216 4 15 22 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 88 216 (accept_3_5 59
  88 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88 216 2 29 44 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 88 216
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 57 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 88 216 8 7 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 88 216 (Polychromatic418967fa.accept_21_13_4_6_1_6668 55 88 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 88 216 2 27 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 88 216 (accept_3_5 53 88 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88 216 4 13 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 88 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 88 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 88 216 2 25 44 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 88 216
  (Polychromatic418967fa.accept_15_4_13_6_1_642 49 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 88 216 8 6 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 88 216 (accept_3_5 47 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88
  216 2 23 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 88 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 88 216 4 11 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 88 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 43 88 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 216 2 21 44 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 216 (accept_3_5 41 88 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 216 8 5 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 216 (Polychromatic418967fa.accept_19_1_12_7_1_12723
  39 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 216 2 19 44 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 216 4 9 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 216 (accept_3_5 35 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  216 2 17 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 88 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 88 216 8 4 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 88 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 88 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 216 2 15 44 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 216 (accept_3_5 29 88 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 216 4 7 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 216 (Polychromatic418967fa.accept_19_8_12_7_1_11458 27 88
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 216 2 13 44 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 216
  (Polychromatic418967fa.accept_13_12_10_8_1_3343 25 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 216 8 3 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 88 216 (accept_3_5 23 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88
  216 2 11 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 88 216 (Polychromatic418967fa.accept_23_21_19_9_1_12755 21 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 88 216 4 5 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 88 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 88 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 216 2 9 44 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 216 (accept_3_5 17 88 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 216 8 2 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 88 216 (Polychromatic418967fa.accept_13_2_10_8_1_1126 15 88 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 216 2 7 44 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 88 216 4 3 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 88 216 (accept_3_5 11 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88
  216 2 5 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  88 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 88 216 8 1 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 88 216 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 88 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 216 2 3 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 216 (accept_3_5 5 88 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 216 4 1 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 88 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 88 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 216 2 1 44 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 216
  (Polychromatic418967fa.accept_19_1_12_7_1_12723 1 88 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87
  216 (allA_succ_of_accept 86 87 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 216 (Polychromatic418967fa.accept_13_7_9_8_1_188 85 87 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 216 3 28 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 83 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 216 (Polychromatic418967fa.accept_13_4_9_8_1_1736 82 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 216 3 27 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 216 (Polychromatic418967fa.accept_11_3_10_7_1_129
  80 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 79 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 216 3 26 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 216 (Polychromatic418967fa.accept_13_12_9_8_1_2595 77 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 216 (Polychromatic418967fa.accept_13_11_9_8_1_1125 76 87
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 216 3 25 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 74 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 73 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 216 3 24 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 71
  87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 216
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 70 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 216 3 23 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 216 (Polychromatic418967fa.accept_13_3_9_8_1_4202 68 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 87 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 216 3 22 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 216 (Polychromatic418967fa.accept_13_12_9_8_1_2595 64 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 216 3 21 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 216 (Polychromatic418967fa.accept_15_2_12_6_1_3063
  62 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 61 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 216 3 20 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 216 (Polychromatic418967fa.accept_13_7_9_8_1_188 59 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 87 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 216 3 19 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 216
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 56 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 216 (Polychromatic418967fa.accept_13_3_9_8_1_4202 55 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 216 3 18 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 53
  87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 216
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 52 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 216 3 17 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 216 (Polychromatic418967fa.accept_13_11_9_8_1_1125 50 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 216 (Polychromatic418967fa.accept_16_1_7_8_1_3422 49 87 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 216 3 16 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 216
  (Polychromatic418967fa.accept_11_3_10_7_1_129 47 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 216 3 15 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 87
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 43 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 216 3 14 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 41 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 216 (Polychromatic418967fa.accept_13_1_9_8_1_1734 40 87 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 216 3 13 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 216
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 38 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 216 3 12 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 216 (Polychromatic418967fa.accept_15_5_12_6_1_639
  35 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 216
  (Polychromatic418967fa.accept_19_15_11_7_1_8711 34 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 216 3 11 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 31 87 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 216 3 10 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 216
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 29 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 216 (Polychromatic418967fa.accept_16_12_7_8_1_1589 28 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 216 3 9 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 216 (Polychromatic418967fa.accept_20_6_7_16_1_5437 26 87 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 216 3 8 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 216 (Polychromatic418967fa.accept_15_7_12_6_1_1327 22 87
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 216 3 7 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 216
  (Polychromatic418967fa.accept_13_7_9_8_1_188 20 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 216 (Polychromatic418967fa.accept_21_19_3_6_1_2281 19 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 216 3 6 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 216 (Polychromatic418967fa.accept_13_4_9_8_1_1736 17 87 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 16 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 216 3 5 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 216 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 87 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 216 3 4 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 216 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 216 3 3 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 216 (Polychromatic418967fa.accept_19_8_11_7_1_11474 8 87 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 216
  (Polychromatic418967fa.accept_13_7_9_8_1_188 7 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 216 3 2 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 216 (Polychromatic418967fa.accept_15_5_12_6_1_639 5 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 87 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 216 3 1 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 87 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 87 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 216
  (allA_succ_of_accept 85 86 216 (accept_3_4 85 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  216 2 42 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 216 (Polychromatic418967fa.accept_17_15_1_12_1_7910 83 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 216 2 41 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 86 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 216 2 40 43 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 216 (accept_3_4 79 86 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 216 2 39 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 216
  (Polychromatic418967fa.accept_15_2_11_6_1_2135 77 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 216 2 38 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 216 (Polychromatic418967fa.accept_19_18_10_7_1_3174 75 86 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 216 2 37 43 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 216 (accept_3_4 73 86 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 216 2 36 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 86 216 2 35 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 86 216 (Polychromatic418967fa.accept_15_9_11_6_1_637 69 86 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 86 216 2 34 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 86 216 (accept_3_4 67 86 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 86 216 2 33 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 86 216 (Polychromatic418967fa.accept_15_5_11_6_1_692
  65 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 216 2 32 43 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 216
  (Polychromatic418967fa.accept_15_3_11_6_1_3083 63 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 216 2 31 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 216 (accept_3_4 61 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 216 2 30 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 86 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 216 2 29 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 216 2 28 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 86 216 (accept_3_4 55 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 216 2 27 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 86 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 216 2 26 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 216
  (Polychromatic418967fa.accept_20_11_6_16_1_8481 51 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 216 2 25 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 216 (accept_3_4 49 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 216 2 24 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 216 (Polychromatic418967fa.accept_15_2_11_6_1_2135 47 86 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 216 2 23 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 216 2 22 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 216 (accept_3_4 43 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 216 2 21 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 216 (Polychromatic418967fa.accept_19_3_10_7_1_5884 41 86 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 216 2 20 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 216 2 19 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 86 216 (accept_3_4 37 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 216 2 18 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 216 (Polychromatic418967fa.accept_11_2_9_7_1_124 35 86 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 216 2 17 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 216
  (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 216 2 16 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 86 216 (accept_3_4 31 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 216 2 15 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 86 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 216 2 14 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 216
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 216 2 13 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 86 216 (accept_3_4 25 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 216 2 12 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 216 (Polychromatic418967fa.accept_17_6_1_12_1_4115 23 86 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 216 2 11 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 216
  (Polychromatic418967fa.accept_20_1_6_16_1_6991 21 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 216 2 10 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 86 216 (accept_3_4 19 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 216 2 9 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 86 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 216 2 8 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 216 2 7 43 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 216 (accept_3_4 13
  86 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 216 2 6 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 86 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 216 2 5 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 216 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 86 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 216 2 4 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 216 (accept_3_4 7 86 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 216 2 3 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 216 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 86 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 216 2 2 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 86
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 216 2 1 43 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 216 (accept_3_4 1 86
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 216
  (allA_succ_of_accept 84 85 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 84 85 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 216 (accept_3_5 83 85 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 216 (Polychromatic418967fa.accept_10_1_5_6_1_649
  81 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 216 (accept_3_5 80
  85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 216 (Polychromatic418967fa.accept_15_3_10_6_1_632 78 85 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 216 (accept_3_5 77 85 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 216 (Polychromatic418967fa.accept_15_1_10_6_1_631 76 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 75
  85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 216 (accept_3_5 74 85
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 216
  (Polychromatic418967fa.accept_19_16_9_7_1_11429 73 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 85 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 85 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 216 (accept_3_5 71 85 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 85 216 (Polychromatic418967fa.accept_11_4_8_7_1_819 70 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 216 (Polychromatic418967fa.accept_10_9_5_6_1_691
  69 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 216 (accept_3_5 68
  85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 216
  (Polychromatic418967fa.accept_13_2_7_8_1_4221 67 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 85 216 (Polychromatic418967fa.accept_13_1_7_8_1_1796 66 85 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 216 (accept_3_5 65 85 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 85 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 64 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 216 (Polychromatic418967fa.accept_14_7_1_6_1_3514
  63 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 216 (accept_3_5 62
  85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 85 216 (Polychromatic418967fa.accept_16_12_5_8_1_2492 60 85 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 216 (accept_3_5 59 85 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 85 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 216
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 57 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 216 (accept_3_5 56 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  85 216 (Polychromatic418967fa.accept_13_3_7_8_1_4192 55 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 85 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 216 (accept_3_5 53 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 216 (Polychromatic418967fa.accept_16_4_5_8_1_2425 52 85 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 85 216 (accept_3_5 50 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  85 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 85 216 (Polychromatic418967fa.accept_11_4_8_7_1_819 48 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 216 (accept_3_5 47 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 216 (Polychromatic418967fa.accept_15_1_10_6_1_631 46 85 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 216
  (Polychromatic418967fa.accept_16_13_5_8_1_5814 45 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 85 216 (accept_3_5 44 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  85 216 (Polychromatic418967fa.accept_16_11_5_8_1_2427 43 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 85 216 (Polychromatic418967fa.accept_13_3_7_8_1_4192 42 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 216 (accept_3_5 41 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 85 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 216
  (Polychromatic418967fa.accept_10_9_5_6_1_691 39 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 85 216 (accept_3_5 38 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  85 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 85 216 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 85 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 216 (accept_3_5 35 85 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 85 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 216 (accept_3_5 32 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 216 (accept_3_5 29 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 216 (Polychromatic418967fa.accept_13_2_7_8_1_4221 28 85 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 216
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 216 (accept_3_5 26 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 216 (Polychromatic418967fa.accept_13_12_7_8_1_1104 25 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 216 (accept_3_5 23 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 216 (Polychromatic418967fa.accept_13_9_7_8_1_1122 22 85 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 21 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 216 (accept_3_5 20 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 216 (Polychromatic418967fa.accept_15_3_10_6_1_632 18 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 216 (accept_3_5 17 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 85 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 216
  (Polychromatic418967fa.accept_11_4_8_7_1_819 15 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 216 (accept_3_5 14 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 216 (Polychromatic418967fa.accept_16_13_5_8_1_5814 13 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 216 (accept_3_5 11 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 216 (Polychromatic418967fa.accept_13_10_7_8_1_1794 10 85 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 216 (accept_3_5 8 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  216 (Polychromatic418967fa.accept_14_7_1_6_1_3514 7 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 85 216 (Polychromatic418967fa.accept_23_6_16_9_1_12754 6 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 216 (accept_3_5 5 85 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 85 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 216
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 216 (accept_3_5 2 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85
  216 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 85 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 85 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84
  216 (allA_succ_of_accept 83 84 216 (Polychromatic418967fa.accept_16_3_4_8_1_3450 83 84 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84 216 2 41 42 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 84 216 3 27 28 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 84 216 4 20 21 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 216
  (Polychromatic418967fa.accept_13_1_6_8_1_208 79 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 84 216 6 13 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 84 216 (Polychromatic418967fa.accept_16_13_4_8_1_4557 77 84 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 216 4 19 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 84 216 3 25 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 84 216 2 37 42 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 84 216
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 73 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 216 12 6 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 216 (Polychromatic418967fa.accept_15_11_9_6_1_1321 71 84 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 216 2 35 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 84 216 3 23 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 84 216 4 17 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 216 (Polychromatic418967fa.accept_13_2_6_8_1_1092
  67 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 216 6 11 14 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 216
  (Polychromatic418967fa.accept_10_5_4_6_1_319 65 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 216 4 16 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 84 216 3 21 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 84 216 2 31 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 84 216 (Polychromatic418967fa.accept_15_1_9_6_1_1323 61 84 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 216 12 5 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 216 (Polychromatic418967fa.accept_15_14_9_6_1_5093
  59 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 216 2 29 42 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 84 216 3 19 28 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 84 216 4 14 21 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 216
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 216 6 9 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 84 216 (Polychromatic418967fa.accept_13_1_6_8_1_208 53 84 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 216 4 13 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 84 216 3 17 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 84 216 2 25 42 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 216
  (Polychromatic418967fa.accept_15_4_9_6_1_627 49 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 216 12 4 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 216 (Polychromatic418967fa.accept_16_15_4_8_1_1562 47 84 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 216 2 23 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 84 216 3 15 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 84 216 4 11 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 216 (Polychromatic418967fa.accept_16_11_4_8_1_3435
  43 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 216 6 7 14 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 216
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 41 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 84 216 4 10 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 84 216 3 13 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 84 216 2 19 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 84 216 (Polychromatic418967fa.accept_13_11_6_8_1_1121 37 84 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 216 12 3 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 35
  84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 216 2 17 42 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 84 216 3 11 28 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 84 216 4 8 21 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 216
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 31 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 216 6 5 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 216 (Polychromatic418967fa.accept_15_14_9_6_1_5093 29 84 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 216 4 7 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 84 216 3 9 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 84 216 2 13 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 25
  84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 216 12 2 7 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 216
  (Polychromatic418967fa.accept_16_7_4_8_1_2487 23 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 84 216 2 11 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 84 216 3 7 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 84 216 4 5 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 84 216 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 84 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 216 6 3 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 216 (Polychromatic418967fa.accept_16_1_4_8_1_3434
  17 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 216 4 4 21 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 84 216 3 5 28 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 216 2 7 42 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 216
  (Polychromatic418967fa.accept_16_13_4_8_1_4557 13 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 216 12 1 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 216 (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 84 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 216 2 5 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 84 216 3 3 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 84 216 4 2 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 216 (Polychromatic418967fa.accept_16_7_4_8_1_2487 7
  84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 216 6 1 14 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 216
  (Polychromatic418967fa.accept_10_5_4_6_1_319 5 84 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 216 4 1 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 84 216 3 1 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 84 216 2 1 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 216 (Polychromatic418967fa.accept_13_1_6_8_1_208 1 84 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 216
  (allA_succ_of_accept 82 83 216 (accept_3_4 82 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 216 (Polychromatic418967fa.accept_13_3_5_8_1_1099 81 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 216 (Polychromatic418967fa.accept_25_5_8_16_1_12753 80 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 216 (accept_3_4 79 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 78 83 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 216
  (Polychromatic418967fa.accept_10_7_3_6_1_644 77 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 216 (accept_3_4 76 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 216 (Polychromatic418967fa.accept_13_10_5_8_1_2555 75 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 216 (Polychromatic418967fa.accept_15_14_8_6_1_2133 74 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 216 (accept_3_4 73 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 216 (Polychromatic418967fa.accept_21_9_20_6_1_9815 72 83
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 216
  (Polychromatic418967fa.accept_17_3_15_12_1_5353 71 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 216 (accept_3_4 70 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 69 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 68 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 216 (accept_3_4 67 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 66 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 216
  (Polychromatic418967fa.accept_17_14_15_12_1_1921 65 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 83 216 (accept_3_4 64 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 83 216 (Polychromatic418967fa.accept_14_7_13_6_1_1177 63 83 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 83 216 (Polychromatic418967fa.accept_13_10_5_8_1_2555 62 83
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 216 (accept_3_4 61 83 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 216 (Polychromatic418967fa.accept_16_12_3_8_1_5729
  60 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 216
  (Polychromatic418967fa.accept_10_9_3_6_1_686 59 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 216 (accept_3_4 58 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 57 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 56 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 216 (accept_3_4 55 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 216 (Polychromatic418967fa.accept_14_12_13_6_1_1140 54 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 216
  (Polychromatic418967fa.accept_13_1_5_8_1_207 53 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 216 (accept_3_4 52 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 216 (Polychromatic418967fa.accept_13_12_5_8_1_1101 51 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 216 (Polychromatic418967fa.accept_44_6_39_40_1_12752 50 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 216 (accept_3_4 49 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 83 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 216
  (Polychromatic418967fa.accept_10_7_3_6_1_644 47 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 216 (accept_3_4 46 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 216 (Polychromatic418967fa.accept_15_14_8_6_1_2133 44 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 216 (accept_3_4 43 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 216 (Polychromatic418967fa.accept_13_3_5_8_1_1099 42 83 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 216
  (Polychromatic418967fa.accept_23_18_14_9_1_12751 41 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 83 216 (accept_3_4 40 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 83 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 83 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 83 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 216 (accept_3_4 37 83 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 216 (Polychromatic418967fa.accept_13_10_5_8_1_2555
  36 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 216
  (Polychromatic418967fa.accept_14_7_13_6_1_1177 35 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 216 (accept_3_4 34 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 216 (Polychromatic418967fa.accept_14_5_13_6_1_3574 33 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 216 (Polychromatic418967fa.accept_15_2_8_6_1_1340 32 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 216 (accept_3_4 31 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 216 (Polychromatic418967fa.accept_21_9_20_6_1_9815 30 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 216
  (Polychromatic418967fa.accept_10_9_3_6_1_686 29 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 216 (accept_3_4 28 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 216 (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 216 (accept_3_4 25 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 216 (Polychromatic418967fa.accept_21_3_20_6_1_5126 24 83
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 216
  (Polychromatic418967fa.accept_11_1_6_7_1_116 23 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 216 (accept_3_4 22 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 216 (Polychromatic418967fa.accept_14_7_13_6_1_1177 21 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 216 (Polychromatic418967fa.accept_16_4_3_8_1_2486 20 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 216 (accept_3_4 19 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 216
  (Polychromatic418967fa.accept_10_7_3_6_1_644 17 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 216 (accept_3_4 16 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 216 (Polychromatic418967fa.accept_21_15_20_6_1_6625 15 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 14 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 216 (accept_3_4 13 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 216
  (Polychromatic418967fa.accept_16_11_3_8_1_4597 11 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 216 (accept_3_4 10 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 216 (accept_3_4 7 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 216 (Polychromatic418967fa.accept_23_6_14_9_1_12750 6 83 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 216
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 5 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 216 (accept_3_4 4 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  216 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 83 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 216 (Polychromatic418967fa.accept_15_2_8_6_1_1340 2 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 216 (accept_3_4 1 83 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83
  216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 216
  (allA_succ_of_accept 81 82 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 82 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 82 216 2 40 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 82 216
  (Polychromatic418967fa.accept_17_11_14_12_1_2995 79 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 82 216 2 39 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 82 216 (accept_3_5 77 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 82 216 2 38 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 82 216 (Polychromatic418967fa.accept_11_9_5_7_1_815 75 82 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 216 2 37 41 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 216
  (Polychromatic418967fa.accept_15_13_7_6_1_682 73 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 82 216 2 36 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 82 216 (accept_3_5 71 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 82 216 2 35 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 82 216 (Polychromatic418967fa.accept_14_13_12_6_1_2735 69 82 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 82 216 2 34 41 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 82 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 82 216 2 33 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 82 216 (accept_3_5 65 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 82 216 2 32 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 82 216 (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 82 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 82 216 2 31 41 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 82 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 82 216 2 30 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 82 216 (accept_3_5 59 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 82 216 2 29 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 82 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 82 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 216 2 28 41 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 216
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 55 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 216 2 27 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 82 216 (accept_3_5 53 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 82 216 2 26 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 82 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 82 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 82 216 2 25 41 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 82 216
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 49 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 82 216 2 24 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 82 216 (accept_3_5 47 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 82 216 2 23 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 82 216 (Polychromatic418967fa.accept_17_11_14_12_1_2995 45 82 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 216 2 22 41 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 82 216 2 21 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 82 216 (accept_3_5 41 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 82 216 2 20 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 82 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 82 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 216 2 19 41 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 216
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 37 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 216 2 18 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 82 216 (accept_3_5 35 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 82 216 2 17 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 82 216 (Polychromatic418967fa.accept_19_14_6_7_1_7223 33 82 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 216 2 16 41 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 216 2 15 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 82 216 (accept_3_5 29 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 82 216 2 14 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 82 216 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 82 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 216 2 13 41 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 216 2 12 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 82 216 (accept_3_5 23 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 82 216 2 11 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 82 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 82 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 216 2 10 41 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 216
  (Polychromatic418967fa.accept_23_19_13_9_1_2861 19 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 216 2 9 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 216 (accept_3_5 17 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  216 2 8 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 216 2 7 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 82 216 (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 82 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 216 2 6 41 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 216 (accept_3_5 11 82 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 216 2 5 41 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 216
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 82 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 216 2 4 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 216 (Polychromatic418967fa.accept_31_7_20_30_1_12749 7 82 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 216 2 3 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 216 (accept_3_5 5 82 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 216 2 2 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 216 (Polychromatic418967fa.accept_19_3_6_7_1_10044 3 82 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 216 2 1 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 82
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 216
  (allA_succ_of_accept 80 81 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 81 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 216 3 26 27 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 216
  (Polychromatic418967fa.accept_10_7_1_6_1_673 77 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 216 (Polychromatic418967fa.accept_13_11_3_8_1_1786 76 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 216 3 25 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 216 (Polychromatic418967fa.accept_11_8_4_7_1_1303
  74 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 73 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 216 9 8 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 216 (Polychromatic418967fa.accept_16_7_1_8_1_5796 71 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 216 (Polychromatic418967fa.accept_13_5_3_8_1_1117 70 81 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 216 3 23 27 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 68 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 67 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 216 3 22 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 65
  81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 216
  (Polychromatic418967fa.accept_23_18_12_9_1_12748 64 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 81 216 9 7 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 81 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 62 81 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 61
  81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 216 3 20 27 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 216 3 19 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 216
  (Polychromatic418967fa.accept_21_14_18_6_1_12747 56 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 81 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 55 81 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 81 216 27 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 81 216 (Polychromatic418967fa.accept_21_11_18_6_1_3521
  53 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 52 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 81 216 3 17 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 81 216 (Polychromatic418967fa.accept_13_11_3_8_1_1786 50 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 216 (Polychromatic418967fa.accept_21_7_18_6_1_9797 49 81
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 216 3 16 27 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 46 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 81 216 9 5 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 81 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 81 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 216
  (Polychromatic418967fa.accept_22_21_15_18_1_4744 43 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 81 216 3 14 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 81 216 (Polychromatic418967fa.accept_11_8_4_7_1_1303 41 81 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 40 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 81 216 3 13 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 81 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 81 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 81 216 9 4 9 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 81 216
  (Polychromatic418967fa.accept_10_5_1_6_1_672 35 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 216 (Polychromatic418967fa.accept_21_13_18_6_1_6676 34 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 216 3 11 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 32
  81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 81 216 3 10 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 81 216 (Polychromatic418967fa.accept_19_10_5_7_1_10007 29 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 216 (Polychromatic418967fa.accept_16_12_1_8_1_5767 28 81
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 216 27 1 3 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 216 3 8 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 81 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 216
  (Polychromatic418967fa.accept_10_2_1_6_1_634 22 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 81 216 3 7 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 81 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 20 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 81 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 216 9 2 9 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 216 3 5 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 216 (Polychromatic418967fa.accept_11_3_4_7_1_114 14 81 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 216
  (Polychromatic418967fa.accept_19_13_5_7_1_12705 13 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 81 216 3 4 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 81 216 (Polychromatic418967fa.accept_13_11_3_8_1_1786 11 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 81 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 216 9 1 9 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 216
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 216 3 2 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 81 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 216
  (Polychromatic418967fa.accept_16_4_1_8_1_835 4 81 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 81 216 3 1 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 81 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 81 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 216 (Polychromatic418967fa.accept_17_1_13_12_1_1084 1 81 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 216
  (allA_succ_of_accept 79 80 216 (accept_3_4 79 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  216 2 39 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  77 80 216 (Polychromatic418967fa.accept_19_1_4_7_1_2018 77 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 216 4 19 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 80 216 (Polychromatic418967fa.accept_13_10_2_8_1_2603 75 80 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 80 216 2 37 40 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 216 (accept_3_4 73 80 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 216 8 9 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 216 (Polychromatic418967fa.accept_13_6_2_8_1_1782
  71 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 80 216 2 35 40 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 216
  (Polychromatic418967fa.accept_19_12_4_7_1_4459 69 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 80 216 4 17 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 80 216 (accept_3_4 67 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80
  216 2 33 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  65 80 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 80 216 8 8 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 80 216 (Polychromatic418967fa.accept_15_3_5_6_1_4005 63 80 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 216 2 31 40 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 216 (accept_3_4 61 80 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 216 4 15 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 216 (Polychromatic418967fa.accept_11_4_3_7_1_828 59
  80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 216 2 29 40 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 216
  (Polychromatic418967fa.accept_15_12_5_6_1_2148 57 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 216 8 7 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 80 216 (accept_3_4 55 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80
  216 2 27 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 80 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 80 216 4 13 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 80 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 80 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 216 2 25 40 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 216 (accept_3_4 49 80 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 216 8 6 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 216 (Polychromatic418967fa.accept_26_21_2_8_1_10996
  47 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 216 2 23 40 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 216
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 216 4 11 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 216 (accept_3_4 43 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  216 2 21 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 80 216 (Polychromatic418967fa.accept_15_11_5_6_1_669 41 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 216 8 5 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 80 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 80 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 216 2 19 40 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 216 (accept_3_4 37 80 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 216 4 9 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 216 (Polychromatic418967fa.accept_19_16_4_7_1_5879 35 80 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 216 2 17 40 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 216
  (Polychromatic418967fa.accept_13_7_2_8_1_1746 33 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 216 8 4 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 216 (accept_3_4 31 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  216 2 15 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 80 216 (Polychromatic418967fa.accept_15_14_5_6_1_6168 29 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 216 4 7 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 216 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 80 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 216 2 13 40 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 216 (accept_3_4 25 80 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 216 8 3 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 80 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 216 2 11 40 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 216
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 216 4 5 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 216 (accept_3_4 19 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  216 2 9 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 216 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 216 8 2 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 216 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 80 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 216 2 7 40 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 216 (accept_3_4 13 80 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 216 4 3 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 80 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 216 2 5 40 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 216 8 1 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 216 (accept_3_4 7 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 216
  2 3 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  216 (Polychromatic418967fa.accept_28_5_24_20_1_10798 5 80 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 80 216 4 1 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 80 216 (Polychromatic418967fa.accept_14_3_10_6_1_1136 3 80 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 216 2 1 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 216 (accept_3_4 1 80 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 80 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 79 216 (allA_succ_of_accept 78 79 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 216 (accept_3_5 77 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 79 216 (Polychromatic418967fa.accept_13_11_1_8_1_1776 76 79
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 75 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 79 216 (accept_3_5 74 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  79 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 79 216 (Polychromatic418967fa.accept_13_7_1_8_1_1778 72 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 216 (accept_3_5 71 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 79 216 (Polychromatic418967fa.accept_13_5_1_8_1_1115 70 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 216
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 69 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 79 216 (accept_3_5 68 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  79 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 79 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 216 (accept_3_5 65 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 79 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 216
  (Polychromatic418967fa.accept_10_3_9_6_1_94 63 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 79 216 (accept_3_5 62 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 216 (Polychromatic418967fa.accept_13_9_1_8_1_1742 61 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 216 (accept_3_5 59 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 216 (Polychromatic418967fa.accept_13_6_1_8_1_1116 58 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 216 (accept_3_5 56 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 55 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 216 (Polychromatic418967fa.accept_15_9_4_6_1_3075 54 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 216 (accept_3_5 53 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 216
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 51 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 216 (accept_3_5 50 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 216 (Polychromatic418967fa.accept_16_1_15_8_1_2411 49 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 216 (Polychromatic418967fa.accept_13_9_1_8_1_1742 48 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 216 (accept_3_5 47 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 216 (accept_3_5 44 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 216 (Polychromatic418967fa.accept_11_9_2_7_1_1298 42 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 216 (accept_3_5 41 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 216 (Polychromatic418967fa.accept_15_10_4_6_1_2129 40 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 216 (accept_3_5 38 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 216 (Polychromatic418967fa.accept_13_11_1_8_1_1776 37 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 216 (accept_3_5 35 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 216 (Polychromatic418967fa.accept_19_15_3_7_1_5875 34 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 216
  (Polychromatic418967fa.accept_10_3_9_6_1_94 33 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 216 (accept_3_5 32 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 216 (Polychromatic418967fa.accept_17_13_11_12_1_4131 30 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 216 (accept_3_5 29 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 216 (Polychromatic418967fa.accept_15_13_4_6_1_3046 28 79
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 216
  (Polychromatic418967fa.accept_22_5_13_18_1_12746 27 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 79 216 (accept_3_5 26 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 79 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 79 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 79 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 216 (accept_3_5 23 79 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 22
  79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 216
  (Polychromatic418967fa.accept_26_21_1_8_1_12745 21 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 216 (accept_3_5 20 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 216 (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 216 (accept_3_5 17 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 216 (Polychromatic418967fa.accept_17_16_11_12_1_2008 16 79 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 216 (accept_3_5 14 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 216 (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 216 (accept_3_5 11 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 79 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 216
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 216 (accept_3_5 8 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  216 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 216 (Polychromatic418967fa.accept_13_6_1_8_1_1116 6 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 216 (accept_3_5 5 79 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 79 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 216 (accept_3_5 2 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  216 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 79 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 216
  (allA_succ_of_accept 77 78 216 (Polychromatic418967fa.accept_14_7_8_6_1_1164 77 78 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 216 2 38 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 78 216 3 25 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 78 216 2 37 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 73 78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 78 216 6 12 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 78 216 (Polychromatic418967fa.accept_15_11_3_6_1_1306 71 78 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 216 2 35 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 78 216 3 23 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 78 216 2 34 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 216
  (Polychromatic418967fa.accept_21_4_15_6_1_8327 67 78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 78 216 6 11 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 78 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 78 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 216 2 32 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 78 216 3 21 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 78 216 2 31 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 216 6 10 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 216 (Polychromatic418967fa.accept_17_8_10_12_1_5335 59 78 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 216 2 29 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 78 216 3 19 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 78 216 2 28 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 216
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 55 78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 216 6 9 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 78 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 53 78 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 216 2 26 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 78 216 3 17 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 78 216 2 25 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 216
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 49 78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 216 6 8 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 78 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 78 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 216 2 23 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 78 216 3 15 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 78 216 2 22 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 216 6 7 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 216 (Polychromatic418967fa.accept_15_11_3_6_1_1306 41 78 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 216 2 20 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 216 3 13 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 216 2 19 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 216 6 6 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 78 216 (Polychromatic418967fa.accept_14_7_8_6_1_1164 35 78 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 216 2 17 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 78 216 3 11 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 78 216 2 16 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 216
  (Polychromatic418967fa.accept_15_1_3_6_1_621 31 78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 216 6 5 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 216 (Polychromatic418967fa.accept_21_8_15_6_1_8247 29 78 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 216 2 14 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 78 216 3 9 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 78 216 2 13 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 216
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 216 6 4 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 78 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 216 2 11 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 78 216 3 7 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 78 216 2 10 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 216 6 3 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 216 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 78 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 216 2 8 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 78 216 3 5 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 78 216 2 7 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 13
  78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 216 6 2 13 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 216
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 216 2 5 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 78 216 3 3 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 78 216 2 4 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 216 (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 78 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 216 6 1 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 78 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 216 2 2 39 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 78 216 3 1 26 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 78 216 2 1 39 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 216
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 78 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 216
  (allA_succ_of_accept 76 77 216 (accept_3_4 76 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 216 (Polychromatic418967fa.accept_13_10_12_8_1_2550 75 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 216 (Polychromatic418967fa.accept_13_9_12_8_1_570 74 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 216 (accept_3_4 73 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 216 (Polychromatic418967fa.accept_13_7_12_8_1_199 72 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 71 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 216 (accept_3_4 70 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 216 (Polychromatic418967fa.accept_13_4_12_8_1_197 69 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 216 (Polychromatic418967fa.accept_15_8_2_6_1_2125 68 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 216 (accept_3_4 67 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 216 (Polychromatic418967fa.accept_13_1_12_8_1_1818 66 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 216
  (Polychromatic418967fa.accept_17_14_9_12_1_5350 65 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 216 (accept_3_4 64 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 216 (Polychromatic418967fa.accept_13_10_12_8_1_2550 62 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 216 (accept_3_4 61 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 216 (Polychromatic418967fa.accept_16_12_13_8_1_2409 60 77
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 216
  (Polychromatic418967fa.accept_13_7_12_8_1_199 59 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 216 (accept_3_4 58 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 216 (Polychromatic418967fa.accept_13_5_12_8_1_198 57 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 216 (Polychromatic418967fa.accept_13_4_12_8_1_197 56 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 216 (accept_3_4 55 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 216 (Polychromatic418967fa.accept_21_12_14_6_1_8214 54 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 53 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 216 (accept_3_4 52 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 51 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 216 (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 216 (accept_3_4 49 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 216 (Polychromatic418967fa.accept_13_9_12_8_1_570 48 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 216
  (Polychromatic418967fa.accept_20_7_17_16_1_6976 47 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 216 (accept_3_4 46 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 216 (Polychromatic418967fa.accept_21_3_14_6_1_11325 45 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 216 (Polychromatic418967fa.accept_13_5_12_8_1_198 44 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 216 (accept_3_4 43 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 216 (Polychromatic418967fa.accept_15_12_2_6_1_2127 42 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 41 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 216 (accept_3_4 40 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 216 (Polychromatic418967fa.accept_17_5_9_12_1_9156 39 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 216 (Polychromatic418967fa.accept_15_8_2_6_1_2125 38 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 216 (accept_3_4 37 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 216 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 216
  (Polychromatic418967fa.accept_13_9_12_8_1_570 35 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 216 (accept_3_4 34 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 216 (Polychromatic418967fa.accept_19_13_1_7_1_5906 32 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 216 (accept_3_4 31 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 216 (Polychromatic418967fa.accept_13_4_12_8_1_197 30 77 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 216
  (Polychromatic418967fa.accept_14_1_7_6_1_3604 29 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 216 (accept_3_4 28 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 216 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 216 (Polychromatic418967fa.accept_15_11_2_6_1_3010 26 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 216 (accept_3_4 25 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 216 (Polychromatic418967fa.accept_21_3_14_6_1_11325 24 77
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 23 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 216 (accept_3_4 22 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 216 (Polychromatic418967fa.accept_13_7_12_8_1_199 20 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 216 (accept_3_4 19 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 216 (Polychromatic418967fa.accept_13_5_12_8_1_198 18 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 216
  (Polychromatic418967fa.accept_13_4_12_8_1_197 17 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 216 (accept_3_4 16 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 216 (Polychromatic418967fa.accept_14_1_7_6_1_3604 15 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 216 (Polychromatic418967fa.accept_13_1_12_8_1_1818 14 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 216 (accept_3_4 13 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 216 (Polychromatic418967fa.accept_15_12_2_6_1_2127 12 77
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 11 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 216 (accept_3_4 10 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 216 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 216 (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 216 (accept_3_4 7 77 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 216 (Polychromatic418967fa.accept_19_6_1_7_1_5872 6 77 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 216
  (Polychromatic418967fa.accept_13_5_12_8_1_198 5 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 216 (accept_3_4 4 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  216 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 77 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 216 (Polychromatic418967fa.accept_19_2_1_7_1_8683 2 77 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 216 (accept_3_4 1 77 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 216 (allA_succ_of_accept 75 76 216 (Polychromatic418967fa.accept_13_10_11_8_1_1770 75 76 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 76 216 2 37 38 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 76 216
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 73 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 76 216 4 18 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 76 216 (accept_3_5 71 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76
  216 2 35 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  69 76 216 (Polychromatic418967fa.accept_11_3_10_7_1_129 69 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 76 216 4 17 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 76 216 (Polychromatic418967fa.accept_15_7_1_6_1_6150 67 76 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 76 216 2 33 38 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 76 216 (accept_3_5 65 76 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76 216 4 16 19 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 76 216
  (Polychromatic418967fa.accept_15_3_1_6_1_206 63 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 76 216 2 31 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 76 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 61 76 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 216 4 15 19 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 216 (accept_3_5 59 76 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 216 2 29 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 216 (Polychromatic418967fa.accept_16_9_12_8_1_1554
  57 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 76 216 4 14 19 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 76 216
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 55 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 76 216 2 27 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 76 216 (accept_3_5 53 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 76 216 4 13 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 76 216 (Polychromatic418967fa.accept_16_3_12_8_1_808 51 76 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 216 2 25 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 216 (Polychromatic418967fa.accept_13_10_11_8_1_1770
  49 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 76 216 4 12 19 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 76 216 (accept_3_5 47
  76 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76 216 2 23 38 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 76 216
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 45 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 76 216 4 11 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 76 216 (Polychromatic418967fa.accept_13_4_11_8_1_1768 43 76 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 216 2 21 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 216 (accept_3_5 41 76 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 216 4 10 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 216 (Polychromatic418967fa.accept_15_9_1_6_1_657 39 76 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 216 2 19 38 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 216
  (Polychromatic418967fa.accept_15_7_1_6_1_6150 37 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 76 216 4 9 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 76 216 (accept_3_5 35 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76
  216 2 17 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 76 216 (Polychromatic418967fa.accept_15_3_1_6_1_206 33 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 76 216 4 8 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 76 216 (Polychromatic418967fa.accept_16_15_12_8_1_4585 31 76 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 76 216 2 15 38 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 76 216 (accept_3_5 29 76 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76 216 4 7 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 76 216 (Polychromatic418967fa.accept_13_1_11_8_1_2562
  27 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 76 216 2 13 38 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 76 216
  (Polychromatic418967fa.accept_11_3_10_7_1_129 25 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 76 216 4 6 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 76 216 (accept_3_5 23 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76
  216 2 11 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 76 216 (Polychromatic418967fa.accept_16_5_12_8_1_2521 21 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 76 216 4 5 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 76 216 (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 76 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 216 2 9 38 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 216 (accept_3_5 17 76 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76 216 4 4 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 76 216 (Polychromatic418967fa.accept_16_15_12_8_1_4585 15 76
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 216 2 7 38 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 216
  (Polychromatic418967fa.accept_16_13_12_8_1_2451 13 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 76 216 4 3 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 76 216 (accept_3_5 11 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76
  216 2 5 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  76 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 76 216 4 2 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 76 216 (Polychromatic418967fa.accept_15_7_1_6_1_6150 7 76 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 216 2 3 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 216 (accept_3_5 5 76 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 216 4 1 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 76 216 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 76 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 216 2 1 38 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 216
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 1 76 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 216
  (allA_succ_of_accept 74 75 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 216 (Polychromatic418967fa.accept_17_5_7_12_1_1951 73 75
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 216 3 24 25 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 216 (Polychromatic418967fa.accept_13_5_10_8_1_1127 70 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 216 3 23 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 216 (Polychromatic418967fa.accept_11_2_9_7_1_124 68
  75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 216 3 22 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 216 (Polychromatic418967fa.accept_19_8_18_7_1_3143 65 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 75 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 216 3 21 25 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 216
  (Polychromatic418967fa.accept_23_16_6_9_1_7840 62 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 61 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 216 3 20 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 59
  75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 216
  (Polychromatic418967fa.accept_19_1_18_7_1_12744 58 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 216 3 19 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 216 (Polychromatic418967fa.accept_13_4_10_8_1_1817 56 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 216 (Polychromatic418967fa.accept_14_13_5_6_1_2747 55 75
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 216 3 18 25 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 216 (Polychromatic418967fa.accept_16_4_11_8_1_1574 52 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 216 3 17 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 50
  75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 216
  (Polychromatic418967fa.accept_10_9_5_6_1_691 49 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 216 3 16 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 216 (Polychromatic418967fa.accept_21_5_12_6_1_11321 47 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 75 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 216 3 15 25 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 216
  (Polychromatic418967fa.accept_10_4_5_6_1_651 44 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 216 3 14 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 41
  75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 216
  (Polychromatic418967fa.accept_21_19_12_6_1_6689 40 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 75 216 3 13 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 216 (Polychromatic418967fa.accept_11_5_9_7_1_411 38 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 216 (Polychromatic418967fa.accept_13_11_10_8_1_1804 37 75
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 216 3 12 25 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 216
  (Polychromatic418967fa.accept_11_2_9_7_1_124 35 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 216 3 11 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 31 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 216 3 10 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 216 (Polychromatic418967fa.accept_13_2_10_8_1_1126 28 75
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 216 3 9 25 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 216
  (Polychromatic418967fa.accept_21_5_12_6_1_11321 26 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 216 3 8 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 216 (Polychromatic418967fa.accept_21_2_12_6_1_6658 23 75 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 216 3 7 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 216 (Polychromatic418967fa.accept_13_7_10_8_1_567 20 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 75 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 216 3 6 25 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 216
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 216 (Polychromatic418967fa.accept_11_5_9_7_1_411 16 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 216 3 5 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 75 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 216
  (Polychromatic418967fa.accept_11_2_9_7_1_124 13 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 216 3 4 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 216 (Polychromatic418967fa.accept_19_10_18_7_1_12729 10 75
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 216 3 3 25 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 216 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 216 3 2 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 216 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 75 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 75 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 216 3 1 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 216 (Polychromatic418967fa.accept_11_2_9_7_1_124 2 75 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 75 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 216 (allA_succ_of_accept
  73 74 216 (accept_3_4 73 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 216 2 36 37 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 216
  (Polychromatic418967fa.accept_49_22_25_20_1_12743 71 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 74 216 2 35 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 74 216 (Polychromatic418967fa.accept_13_4_9_8_1_1736 69 74 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 216 2 34 37 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 216 (accept_3_4 67 74 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 216 2 33 37 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 74 216 2 32 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 74 216 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 74 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 74 216 2 31 37 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 74 216 (accept_3_4 61 74 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74 216 2 30 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 74 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 59
  74 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 216 2 29 37 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 216
  (Polychromatic418967fa.accept_21_15_11_6_1_5121 57 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 216 2 28 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 74 216 (accept_3_4 55 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 74 216 2 27 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 216 (Polychromatic418967fa.accept_13_1_9_8_1_1734 53 74 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 216 2 26 37 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 216 2 25 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 74 216 (accept_3_4 49 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 74 216 2 24 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 74 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 74 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 216 2 23 37 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 216 2 22 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 74 216 (accept_3_4 43 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 74 216 2 21 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 74 216 (Polychromatic418967fa.accept_21_20_11_6_1_8306 41 74 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 216 2 20 37 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 216
  (Polychromatic418967fa.accept_15_9_14_6_1_3004 39 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 216 2 19 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 74 216 (accept_3_4 37 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 74 216 2 18 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 74 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 74 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 216 2 17 37 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 216 2 16 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 74 216 (accept_3_4 31 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 216 2 15 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 216 (Polychromatic418967fa.accept_13_3_9_8_1_4202 29 74 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 216 2 14 37 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 216
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 216 2 13 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 74 216 (accept_3_4 25 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 216 2 12 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 74 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 216 2 11 37 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 216
  (Polychromatic418967fa.accept_19_2_17_7_1_8735 21 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 216 2 10 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 216 (accept_3_4 19 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 216 2 9 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 74 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 216 2 8 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 15
  74 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 216 2 7 37 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 216 (accept_3_4 13
  74 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 216 2 6 37 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 216
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 74 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 74 216 2 5 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 74 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 74 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 216 2 4 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 216 (accept_3_4 7 74 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 216 2 3 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 74 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 216 2 2 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 74
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 216 2 1 37 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 216 (accept_3_4 1 74
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 216 (allA_succ_of_accept
  72 73 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 216 (accept_3_5 71 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 216 (Polychromatic418967fa.accept_25_20_23_16_1_12742 70 73 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 216 (Polychromatic418967fa.accept_10_9_3_6_1_686
  69 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 216 (accept_3_5 68
  73 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 67 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 73 216 (Polychromatic418967fa.accept_14_10_3_6_1_2728 66 73 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 73 216 (accept_3_5 65 73 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 73 216 (Polychromatic418967fa.accept_15_4_13_6_1_642 64 73 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 73 216 (Polychromatic418967fa.accept_16_15_9_8_1_2440
  63 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 216 (accept_3_5 62
  73 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 216
  (Polychromatic418967fa.accept_17_10_5_12_1_4101 61 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 73 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 73 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 73 216 (accept_3_5 59 73 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 73 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 73 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 73 216 (Polychromatic418967fa.accept_10_7_3_6_1_644
  57 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 216 (accept_3_5 56
  73 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 216
  (Polychromatic418967fa.accept_16_7_9_8_1_829 55 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 73 216 (Polychromatic418967fa.accept_21_12_10_6_1_1191 54 73 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 216 (accept_3_5 53 73 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 73 216 (Polychromatic418967fa.accept_14_10_3_6_1_2728 52 73 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 73 216 (accept_3_5 50 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  73 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 73 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 73 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 216 (accept_3_5 47 73 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 73 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 73 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 216
  (Polychromatic418967fa.accept_22_1_7_18_1_12741 45 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 73 216 (accept_3_5 44 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  73 216 (Polychromatic418967fa.accept_17_9_5_12_1_6606 43 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 73 216 (Polychromatic418967fa.accept_17_8_5_12_1_7925 42 73 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 216 (accept_3_5 41 73 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 216 (Polychromatic418967fa.accept_19_2_16_7_1_11424 40 73
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 73 216 (accept_3_5 38 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  73 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 73 216 (Polychromatic418967fa.accept_16_4_9_8_1_2509 36 73 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 216 (accept_3_5 35 73 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 216 (Polychromatic418967fa.accept_15_4_13_6_1_642 34 73 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 216
  (Polychromatic418967fa.accept_16_1_9_8_1_2438 33 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 73 216 (accept_3_5 32 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 216 (Polychromatic418967fa.accept_16_15_9_8_1_2440 31 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 73 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 216 (accept_3_5 29 73 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 73 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 216
  (Polychromatic418967fa.accept_10_7_3_6_1_644 27 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 216 (accept_3_5 26 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 216 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 73 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 216 (accept_3_5 23 73 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 216 (Polychromatic418967fa.accept_15_7_13_6_1_696 22 73 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 216
  (Polychromatic418967fa.accept_19_2_16_7_1_11424 21 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 216 (accept_3_5 20 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 73 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 216 (accept_3_5 17 73 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 73 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 216
  (Polychromatic418967fa.accept_16_15_9_8_1_2440 15 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 216 (accept_3_5 14 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 216 (Polychromatic418967fa.accept_22_13_7_18_1_12740 13 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 216 (Polychromatic418967fa.accept_16_12_9_8_1_2508 12 73 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 216 (accept_3_5 11 73 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 216 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 73
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 216 (accept_3_5 8 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  216 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 216 (Polychromatic418967fa.accept_19_6_16_7_1_11433 6 73 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 216 (accept_3_5 5 73 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 73 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 216 (Polychromatic418967fa.accept_20_3_13_16_1_641
  3 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 216 (accept_3_5 2 73
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 216
  (Polychromatic418967fa.accept_16_1_9_8_1_2438 1 73 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 73 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 216
  (allA_succ_of_accept 71 72 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 72 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 216 2 35 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 72 216 3 23 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 72 216 4 17 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 67
  72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 216 6 11 12 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 216
  (Polychromatic418967fa.accept_15_5_12_6_1_639 65 72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 72 216 8 8 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 72 216 9 7 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 72 216 2 31 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 72 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 61 72 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 216 12 5 6 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 59
  72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 216 2 29 36 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 72 216 3 19 24 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 72 216 8 7 9 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 216
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 55 72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 216 18 3 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 72 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 216 4 13 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 72 216 3 17 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 72 216 2 25 36 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 216
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 49 72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 72 216 24 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 72 216 (Polychromatic418967fa.accept_15_2_12_6_1_3063 47 72 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 216 2 23 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 72 216 9 5 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 72 216 4 11 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 43
  72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 216 6 7 12 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 41 72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 216 8 5 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 72 216 3 13 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 72 216 2 19 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 72 216 (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 72 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 216 36 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 216 (Polychromatic418967fa.accept_13_9_7_8_1_1122
  35 72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 216 2 17 36 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 72 216 3 11 24 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 72 216 8 4 9 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 216 6 5 12 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 72 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 72 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 216 4 7 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 72 216 9 3 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 72 216 2 13 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 25
  72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 216 24 1 3 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 216
  (Polychromatic418967fa.accept_11_1_6_7_1_116 23 72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 72 216 2 11 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 72 216 3 7 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 72 216 4 5 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 216 (Polychromatic418967fa.accept_17_2_4_12_1_6587 19 72 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 216 18 1 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 216 8 2 9 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 72 216 3 5 24 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 72 216 2 7 36 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 216
  (Polychromatic418967fa.accept_19_13_15_7_1_5843 13 72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 216 12 1 6 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 216 2 5 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 72 216 9 1 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 72 216 8 1 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 216 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7
  72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 216 6 1 12 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 216
  (Polychromatic418967fa.accept_15_5_12_6_1_639 5 72 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 216 4 1 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 72 216 3 1 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 72 216 2 1 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 72 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 216 (allA_succ_of_accept 70
  71 216 (accept_3_4 70 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 216
  (Polychromatic418967fa.accept_15_9_11_6_1_637 69 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 71 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 216 (accept_3_4 67 71 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 216 (Polychromatic418967fa.accept_13_1_6_8_1_208 66 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 65
  71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 216 (accept_3_4 64 71
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 216
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 63 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 71 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 62 71 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 216 (accept_3_4 61 71 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 71 216 (Polychromatic418967fa.accept_16_12_7_8_1_1589 60 71 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 216
  (Polychromatic418967fa.accept_17_8_3_12_1_5354 59 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 216 (accept_3_4 58 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 57 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 216 (Polychromatic418967fa.accept_19_18_14_7_1_5864 56 71 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 216 (accept_3_4 55 71 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 71 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 216
  (Polychromatic418967fa.accept_11_9_5_7_1_815 53 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 216 (accept_3_4 52 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 216 (Polychromatic418967fa.accept_13_11_6_8_1_1121 50 71 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 216 (accept_3_4 49 71 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 216 (Polychromatic418967fa.accept_15_3_11_6_1_3083 48 71
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 216 (accept_3_4 46 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 216 (accept_3_4 43 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 71 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 216
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 41 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 216 (accept_3_4 40 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 216 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 216 (Polychromatic418967fa.accept_20_18_11_16_1_6973 38 71 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 216 (accept_3_4 37 71 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 216 (Polychromatic418967fa.accept_16_4_7_8_1_5753 36 71 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 216
  (Polychromatic418967fa.accept_10_5_1_6_1_672 35 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 216 (accept_3_4 34 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 32 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 216 (accept_3_4 31 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 71 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 216
  (Polychromatic418967fa.accept_19_10_14_7_1_11440 29 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 71 216 (accept_3_4 28 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 71 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 71 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 71 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 216 (accept_3_4 25 71 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 216 (Polychromatic418967fa.accept_13_11_6_8_1_1121
  24 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 216 (accept_3_4 22 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 216 (Polychromatic418967fa.accept_14_7_1_6_1_3514 21 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 216 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 216 (accept_3_4 19 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 216 (Polychromatic418967fa.accept_15_3_11_6_1_3083 18 71 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 216
  (Polychromatic418967fa.accept_10_7_1_6_1_673 17 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 216 (accept_3_4 16 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 216 (Polychromatic418967fa.accept_13_1_6_8_1_208 14 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 216 (accept_3_4 13 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 216
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 216 (accept_3_4 10 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 216 (Polychromatic418967fa.accept_17_8_3_12_1_5354 8 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 216 (accept_3_4 7 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 216 (Polychromatic418967fa.accept_19_6_14_7_1_5902 6 71 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 216 (accept_3_4 4 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  216 (Polychromatic418967fa.accept_15_3_11_6_1_3083 3 71 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 71 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 216 (accept_3_4 1 71 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 71 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 70 216 (allA_succ_of_accept 69 70 216 (Polychromatic418967fa.accept_11_3_4_7_1_114 69 70 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 70 216 2 34 35 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 70 216
  (Polychromatic418967fa.accept_21_4_7_6_1_3605 67 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 70 216 2 33 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 70 216 (accept_3_5 65 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 70 216 2 32 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 70 216 (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 70 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 70 216 2 31 35 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 216
  (Polychromatic418967fa.accept_15_1_10_6_1_631 61 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 70 216 2 30 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 70 216 (accept_3_5 59 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 70 216 2 29 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 70 216 (Polychromatic418967fa.accept_15_12_10_6_1_2134 57 70 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 216 2 28 35 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 70 216
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 55 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 70 216 2 27 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 70 216 (accept_3_5 53 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 70 216 2 26 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 70 216 (Polychromatic418967fa.accept_13_12_5_8_1_1101 51 70 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 216 2 25 35 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 216
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 49 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 70 216 2 24 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 70 216 (accept_3_5 47 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 70 216 2 23 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 70 216 (Polychromatic418967fa.accept_20_5_10_16_1_9890 45 70 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 70 216 2 22 35 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 216
  (Polychromatic418967fa.accept_19_5_13_7_1_8689 43 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 216 2 21 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 70 216 (accept_3_5 41 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 70 216 2 20 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 70 216 (Polychromatic418967fa.accept_19_1_13_7_1_993 39 70 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 216 2 19 35 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 216
  (Polychromatic418967fa.accept_21_16_7_6_1_6687 37 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 216 2 18 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 70 216 (accept_3_5 35 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 70 216 2 17 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 70 216 (Polychromatic418967fa.accept_15_3_10_6_1_632 33 70 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 216 2 16 35 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 216
  (Polychromatic418967fa.accept_15_1_10_6_1_631 31 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 70 216 2 15 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 70 216 (accept_3_5 29 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 70 216 2 14 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 70 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 70 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 216 2 13 35 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 70 216
  (Polychromatic418967fa.accept_11_3_4_7_1_114 25 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 70 216 2 12 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 70 216 (accept_3_5 23 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 70 216 2 11 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 70 216 (Polychromatic418967fa.accept_17_4_2_12_1_6554 21 70 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 216 2 10 35 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 216
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 216 2 9 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 216 (accept_3_5 17 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70
  216 2 8 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  70 216 (Polychromatic418967fa.accept_19_15_13_7_1_7246 15 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 70 216 2 7 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 70 216 (Polychromatic418967fa.accept_21_13_7_6_1_3656 13 70 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 216 2 6 35 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 216 (accept_3_5 11 70 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 216 2 5 35 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 216
  (Polychromatic418967fa.accept_19_9_13_7_1_5830 9 70 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 216 2 4 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 216 (Polychromatic418967fa.accept_17_7_2_12_1_1069 7 70 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 216 2 3 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 216 (accept_3_5 5 70 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 70 216 2 2 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 70 216 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 70 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 216 2 1 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 1
  70 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 216 (allA_succ_of_accept 68 69
  216 (Polychromatic418967fa.accept_14_12_13_6_1_1140 68 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 69 216 (Polychromatic418967fa.accept_16_3_5_8_1_4543 67 69 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 216 3 22 23 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 65 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 216 (Polychromatic418967fa.accept_13_12_4_8_1_1120 64 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 216 3 21 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 216 (Polychromatic418967fa.accept_13_10_4_8_1_2570
  62 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 216
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 61 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 216 3 20 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 216 (Polychromatic418967fa.accept_11_4_3_7_1_828 59 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 216 (Polychromatic418967fa.accept_19_1_12_7_1_12723 58 69
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 216 3 19 23 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 216
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 56 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 55 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 216 3 18 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 53
  69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 216
  (Polychromatic418967fa.accept_16_4_5_8_1_2425 52 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 216 3 17 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 216 (Polychromatic418967fa.accept_13_11_4_8_1_1098 50 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 216 (Polychromatic418967fa.accept_13_10_4_8_1_2570 49 69
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 216 3 16 23 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 216
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 47 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 216 (Polychromatic418967fa.accept_15_1_9_6_1_1323 46 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 216 3 15 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 216 (Polychromatic418967fa.accept_15_14_9_6_1_5093
  44 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 216
  (Polychromatic418967fa.accept_10_3_9_6_1_94 43 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 216 3 14 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 216 (Polychromatic418967fa.accept_15_11_9_6_1_1321 41 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 216 (Polychromatic418967fa.accept_14_12_13_6_1_1140 40 69
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 216 3 13 23 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 216
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 38 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 216 (Polychromatic418967fa.accept_11_4_3_7_1_828 37 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 216 3 12 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 35
  69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 216
  (Polychromatic418967fa.accept_15_4_9_6_1_627 34 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 216 3 11 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 216 (Polychromatic418967fa.accept_11_10_3_7_1_2564 32 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 216 (Polychromatic418967fa.accept_15_1_9_6_1_1323 31 69 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 216 3 10 23 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 216
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 29 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 216 (Polychromatic418967fa.accept_16_12_5_8_1_2492 28 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 216 3 9 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 216 (Polychromatic418967fa.accept_11_4_3_7_1_828 26 69 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 25 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 216 3 8 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 23 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 216 (Polychromatic418967fa.accept_13_9_4_8_1_1752 22 69 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 216 3 7 23 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 216
  (Polychromatic418967fa.accept_16_4_5_8_1_2425 20 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 216 (Polychromatic418967fa.accept_14_5_13_6_1_3574 19 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 216 3 6 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 216 (Polychromatic418967fa.accept_25_17_19_16_1_11100 17 69
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 216
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 16 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 216 3 5 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 216 (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 69 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 216 3 4 23 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 216
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 216 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 216 3 3 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 216 (Polychromatic418967fa.accept_19_8_12_7_1_11458 8 69 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 216
  (Polychromatic418967fa.accept_14_7_13_6_1_1177 7 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 216 3 2 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 216 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 69 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 216 3 1 23 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 216
  (Polychromatic418967fa.accept_29_2_11_13_1_12739 2 69 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 216 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 69 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 216 (allA_succ_of_accept 67 68 216 (accept_3_4 67 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 68 216 2 33 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 68 216 (Polychromatic418967fa.accept_16_1_4_8_1_3434 65 68 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 68 216 4 16 17 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 68 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 68 216 2 31 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 68 216 (accept_3_4 61 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 68 216 4 15 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 68 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 59 68 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 216 2 29 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 57
  68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 68 216 4 14 17 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 68 216 (accept_3_4 55
  68 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68 216 2 27 34 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 68 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 68 216 4 13 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 68 216 (Polychromatic418967fa.accept_16_3_4_8_1_3450 51 68 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 216 2 25 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 216 (accept_3_4 49 68 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 216 4 12 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 216 (Polychromatic418967fa.accept_15_2_8_6_1_1340 47 68 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 216 2 23 34 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 216
  (Polychromatic418967fa.accept_16_13_4_8_1_4557 45 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 68 216 4 11 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 68 216 (accept_3_4 43 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68
  216 2 21 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 68 216 (Polychromatic418967fa.accept_14_13_12_6_1_2735 41 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 68 216 4 10 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 68 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 68 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 216 2 19 34 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 216 (accept_3_4 37 68 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 216 4 9 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 68 216 (Polychromatic418967fa.accept_13_9_3_8_1_573 35
  68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 216 2 17 34 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 216 4 8 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 216 (accept_3_4 31 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  216 2 15 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 68 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 216 4 7 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 68 216 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 68 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 216 2 13 34 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 216 (accept_3_4 25 68 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 216 4 6 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 23
  68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 216 2 11 34 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 216
  (Polychromatic418967fa.accept_16_5_4_8_1_1560 21 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 216 4 5 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 216 (accept_3_4 19 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  216 2 9 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 216 (Polychromatic418967fa.accept_15_2_8_6_1_1340 17 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 216 4 4 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 68 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 216 2 7 34 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 216 (accept_3_4 13 68 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 216 4 3 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 68 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 216 2 5 34 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 216
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 216 4 2 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 216 (accept_3_4 7 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 216
  2 3 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  216 (Polychromatic418967fa.accept_13_5_3_8_1_1117 5 68 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 68 216 4 1 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 68 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 68 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 216 2 1 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 216 (accept_3_4 1 68 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 68 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  67 216 (allA_succ_of_accept 66 67 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 67 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 67 216 (accept_3_5 65 67 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 67 216 (Polychromatic418967fa.accept_17_13_16_12_1_6562 64 67 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 67 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 63 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 67 216 (accept_3_5 62 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  67 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 67 216 (Polychromatic418967fa.accept_16_12_3_8_1_5729 60 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 67 216 (accept_3_5 59 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 67 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 67 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 67 216
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 57 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 67 216 (accept_3_5 56 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  67 216 (Polychromatic418967fa.accept_19_17_10_7_1_11430 55 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 67 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 67 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 67 216 (accept_3_5 53 67 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 67 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 67 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 67 216 (accept_3_5 50 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  67 216 (Polychromatic418967fa.accept_13_10_2_8_1_2603 49 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 67 216 (Polychromatic418967fa.accept_23_2_21_9_1_12738 48 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 67 216 (accept_3_5 47 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 67 216 (Polychromatic418967fa.accept_13_7_2_8_1_1746 46 67 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 67 216 (accept_3_5 44 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  67 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 43 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 67 216 (Polychromatic418967fa.accept_15_12_7_6_1_4013 42 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 67 216 (accept_3_5 41 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 67 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 67 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 67 216
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 67 216 (accept_3_5 38 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  67 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 67 216 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 216 (accept_3_5 35 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 216 (Polychromatic418967fa.accept_21_13_4_6_1_6668 34 67
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 216 (accept_3_5 32 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 67 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 216 (accept_3_5 29 67 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 216 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 216
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 216 (accept_3_5 26 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 216 (Polychromatic418967fa.accept_23_2_21_9_1_12738 25 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 67 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 216 (accept_3_5 23 67 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 216 (Polychromatic418967fa.accept_19_3_10_7_1_5884 22 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 21 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 216 (accept_3_5 20 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 216 (Polychromatic418967fa.accept_17_1_16_12_1_5298 18 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 216 (accept_3_5 17 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 67 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 216
  (Polychromatic418967fa.accept_21_15_4_6_1_11286 15 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 216 (accept_3_5 14 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 67 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 216 (accept_3_5 11 67 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 216 (accept_3_5 8 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  216 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 67 216 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 67 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 216 (accept_3_5 5 67 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 216 (Polychromatic418967fa.accept_16_4_3_8_1_2486 4 67 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 67 216 (accept_3_5 2 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67
  216 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 67 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 67 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 216
  (allA_succ_of_accept 65 66 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 66 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 216 2 32 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 66 216 3 21 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 66 216 2 31 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 216
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 61 66 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 216 6 10 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 216 (Polychromatic418967fa.accept_13_7_1_8_1_1778 59 66 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 216 2 29 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 66 216 3 19 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 66 216 2 28 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 216
  (Polychromatic418967fa.accept_19_17_9_7_1_3171 55 66 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 216 6 9 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 66 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 216 2 26 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 66 216 3 17 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 66 216 2 25 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 216
  (Polychromatic418967fa.accept_19_11_9_7_1_4447 49 66 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 216 6 8 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 66 216 (Polychromatic418967fa.accept_20_7_6_16_1_11369 47 66 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 216 2 23 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 66 216 3 15 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 66 216 2 22 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 216
  (Polychromatic418967fa.accept_19_5_9_7_1_3137 43 66 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 216 6 7 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 216 (Polychromatic418967fa.accept_20_1_6_16_1_6991 41 66 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 216 2 20 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 66 216 3 13 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 66 216 2 19 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 66 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 216 6 6 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 216 (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 66 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 216 2 17 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 216 3 11 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 216 2 16 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 216
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 31 66 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 216 6 5 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 216 (Polychromatic418967fa.accept_19_10_9_7_1_8696 29 66 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 216 2 14 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 66 216 3 9 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 66 216 2 13 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 66 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 216 6 4 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 66 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 216 2 11 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 216 3 7 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 66 216 2 10 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 216
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 66 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 216 6 3 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 216 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 66 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 216 2 8 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 216 3 5 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 216 2 7 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 216 (Polychromatic418967fa.accept_19_13_9_7_1_2038
  13 66 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 216 6 2 11 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 66 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 216 2 5 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 66 216 3 3 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 66 216 2 4 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 216 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 66 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 216 6 1 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 216 (Polychromatic418967fa.accept_13_5_1_8_1_1115 5 66 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 216 2 2 33 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 216 3 1 22 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 216 2 1 33 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 216
  (Polychromatic418967fa.accept_17_1_15_12_1_7907 1 66 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 216
  (allA_succ_of_accept 64 65 216 (accept_3_4 64 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 216 (Polychromatic418967fa.accept_15_3_5_6_1_4005 63 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 216 (Polychromatic418967fa.accept_17_11_14_12_1_2995 62 65 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 216 (accept_3_4 61 65 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 65 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 216 (accept_3_4 58 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 216 (Polychromatic418967fa.accept_15_11_5_6_1_669 56 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 216 (accept_3_4 55 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 65 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 216 (accept_3_4 52 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 51 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 216 (accept_3_4 49 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 216 (Polychromatic418967fa.accept_15_3_5_6_1_4005 48 65 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 216
  (Polychromatic418967fa.accept_11_3_10_7_1_129 47 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 216 (accept_3_4 46 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 44 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 216 (accept_3_4 43 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 216 (Polychromatic418967fa.accept_15_12_5_6_1_2148 42 65 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 41 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 216 (accept_3_4 40 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 216 (accept_3_4 37 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 65 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 216
  (Polychromatic418967fa.accept_19_16_8_7_1_7226 35 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 216 (accept_3_4 34 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 216 (Polychromatic418967fa.accept_15_3_5_6_1_4005 33 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 216 (accept_3_4 31 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 216 (Polychromatic418967fa.accept_19_11_8_7_1_11423 30 65 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 216 (accept_3_4 28 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 216 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 216 (Polychromatic418967fa.accept_15_11_5_6_1_669 26 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 216 (accept_3_4 25 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 216
  (Polychromatic418967fa.accept_16_7_1_8_1_5796 23 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 216 (accept_3_4 22 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 216 (Polychromatic418967fa.accept_16_4_1_8_1_835 20 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 216 (accept_3_4 19 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 65 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 216 (accept_3_4 16 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 216 (accept_3_4 13 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 216 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 65 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 216 (accept_3_4 10 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 216 (accept_3_4 7 65 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 216 (Polychromatic418967fa.accept_19_6_8_7_1_10023 6 65 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 216
  (Polychromatic418967fa.accept_23_5_19_9_1_12737 5 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 216 (accept_3_4 4 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  216 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 65 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 216 (Polychromatic418967fa.accept_26_2_13_8_1_12736 2 65 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 216 (accept_3_4 1 65 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 216
  (allA_succ_of_accept 63 64 216 (Polychromatic418967fa.accept_14_7_8_6_1_1164 63 64 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 64 216 2 31 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 64 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 61
  64 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 216 4 15 16 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 216 (accept_3_5 59
  64 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 216 2 29 32 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 216
  (Polychromatic418967fa.accept_11_2_9_7_1_124 57 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 216 8 7 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 55 64 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 216 2 27 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 216 (accept_3_5 53 64 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 216 4 13 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 64 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 216 2 25 32 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 216
  (Polychromatic418967fa.accept_11_5_9_7_1_411 49 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 216 8 6 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 216 (accept_3_5 47 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  216 2 23 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 64 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 216 4 11 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 216 (Polychromatic418967fa.accept_13_4_12_8_1_197 43 64 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 216 2 21 32 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 216 (accept_3_5 41 64 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 216 8 5 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 216 (Polychromatic418967fa.accept_15_9_4_6_1_3075
  39 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 216 2 19 32 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 216 4 9 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 216 (accept_3_5 35 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  216 2 17 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 64 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 216 8 4 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 64 216 (Polychromatic418967fa.accept_13_5_12_8_1_198 31 64 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 216 2 15 32 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 216 (accept_3_5 29 64 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 216 4 7 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 216 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 64 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 216 2 13 32 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 216
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 216 8 3 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 64 216 (accept_3_5 23 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64
  216 2 11 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 64 216 (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 64 216 4 5 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 64 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 64 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 216 2 9 32 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 216 (accept_3_5 17 64 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 216 8 2 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 64 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 64 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 216 2 7 32 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 216
  (Polychromatic418967fa.accept_11_2_9_7_1_124 13 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 216 4 3 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 216 (accept_3_5 11 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64
  216 2 5 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  64 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 64 216 8 1 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 64 216 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 64 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 216 2 3 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 216 (accept_3_5 5 64 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 216 4 1 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 64 216 (Polychromatic418967fa.accept_21_3_1_6_1_1162 3 64 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 216 2 1 32 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 216
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 64 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 216
  (allA_succ_of_accept 62 63 216 (Polychromatic418967fa.accept_13_10_11_8_1_1770 62 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 61 63 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 216 3 20 21 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 216
  (Polychromatic418967fa.accept_10_9_3_6_1_686 59 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 63 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 63 216 3 19 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 63 216 (Polychromatic418967fa.accept_13_4_11_8_1_1768
  56 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 216
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 55 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 63 216 9 6 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 63 216 (Polychromatic418967fa.accept_13_1_11_8_1_2562 53 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 216 (Polychromatic418967fa.accept_16_4_15_8_1_2413 52 63
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 216 3 17 21 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 216
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 63 216 3 16 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 47
  63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 216
  (Polychromatic418967fa.accept_15_1_3_6_1_621 46 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 63 216 9 5 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 63 216 (Polychromatic418967fa.accept_16_12_15_8_1_4586 44 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 216 (Polychromatic418967fa.accept_13_4_11_8_1_1768 43 63
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 216 3 14 21 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 216
  (Polychromatic418967fa.accept_14_13_7_6_1_3525 41 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 216 (Polychromatic418967fa.accept_13_1_11_8_1_2562 40 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 216 3 13 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 38
  63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 216
  (Polychromatic418967fa.accept_10_7_3_6_1_644 37 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 63 216 9 4 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 63 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 216 (Polychromatic418967fa.accept_30_4_3_6_1_12735 34 63
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 216 3 11 21 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 216
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 32 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 216 (Polychromatic418967fa.accept_15_1_3_6_1_621 31 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 216 3 10 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 29
  63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 216
  (Polychromatic418967fa.accept_10_8_3_6_1_685 28 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 63 216 9 3 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 216 (Polychromatic418967fa.accept_11_4_8_7_1_819 26 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 216 (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 63
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 216 3 8 21 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 216
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 23 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 22 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 216 3 7 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 216 (Polychromatic418967fa.accept_15_5_3_6_1_2128 20 63 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 216
  (Polychromatic418967fa.accept_10_9_3_6_1_686 19 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 63 216 9 2 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 63 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 17 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 216 (Polychromatic418967fa.accept_13_3_11_8_1_1094 16 63
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 216 3 5 21 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 216
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 14 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 216 (Polychromatic418967fa.accept_14_13_7_6_1_3525 13 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 216 3 4 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 216 (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 63 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 216
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 216 9 1 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 63 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 216 3 2 21 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 216
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 216 (Polychromatic418967fa.accept_11_4_8_7_1_819 4 63 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 216 3 1 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 216 (Polychromatic418967fa.accept_23_2_17_9_1_12734 2 63 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 216
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 1 63 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 216 (allA_succ_of_accept
  61 62 216 (accept_3_4 61 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 216 2 30 31 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 216
  (Polychromatic418967fa.accept_13_7_10_8_1_567 59 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 216 2 29 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 62 216 (Polychromatic418967fa.accept_13_5_10_8_1_1127 57 62 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 216 2 28 31 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 216 (accept_3_4 55 62 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 216 2 27 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 216 (Polychromatic418967fa.accept_15_8_2_6_1_2125
  53 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 216 2 26 31 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 216 2 25 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 62 216 (accept_3_4 49 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 62 216 2 24 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 62 216 (Polychromatic418967fa.accept_17_13_11_12_1_4131 47 62 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 216 2 23 31 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 216
  (Polychromatic418967fa.accept_21_3_20_6_1_5126 45 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 216 2 22 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 216 (accept_3_4 43 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 216 2 21 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 62 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 216 2 20 31 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 216
  (Polychromatic418967fa.accept_21_18_20_6_1_6640 39 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 216 2 19 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 216 (accept_3_4 37 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 216 2 18 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 216 (Polychromatic418967fa.accept_21_14_20_6_1_9817 35 62 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 216 2 17 31 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 216
  (Polychromatic418967fa.accept_13_7_10_8_1_567 33 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 216 2 16 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 62 216 (accept_3_4 31 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 62 216 2 15 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 216 (Polychromatic418967fa.accept_19_10_5_7_1_10007 29 62 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 216 2 14 31 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 216
  (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 216 2 13 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 62 216 (accept_3_4 25 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 216 2 12 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 216 (Polychromatic418967fa.accept_15_8_2_6_1_2125 23 62 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 216 2 11 31 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 216 2 10 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 216 (accept_3_4 19 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 216 2 9 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 216 (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 62 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 216 2 8 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 216 (Polychromatic418967fa.accept_13_2_10_8_1_1126
  15 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 216 2 7 31 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 216 (accept_3_4 13
  62 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 216 2 6 31 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 11 62 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 216 2 5 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 216 (Polychromatic418967fa.accept_19_9_5_7_1_5853 9 62 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 216 2 4 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 216 (accept_3_4 7 62 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 216 2 3 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 216 (Polychromatic418967fa.accept_13_5_10_8_1_1127 5 62 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 216 2 2 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 216 (Polychromatic418967fa.accept_19_3_5_7_1_12733 3
  62 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 216 2 1 31 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 216 (accept_3_4 1 62
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 216 (allA_succ_of_accept 60 61 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 216 (accept_3_5 59 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 216 (Polychromatic418967fa.accept_19_1_4_7_1_2018 58 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 216 (accept_3_5 56 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 55 61 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 216
  (Polychromatic418967fa.accept_15_9_1_6_1_657 54 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 216 (accept_3_5 53 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 216 (Polychromatic418967fa.accept_13_12_9_8_1_2595 51 61 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 216 (accept_3_5 50 61 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 216 (Polychromatic418967fa.accept_19_11_4_7_1_1029 49 61
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 216
  (Polychromatic418967fa.accept_15_3_1_6_1_206 48 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 216 (accept_3_5 47 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 216 (accept_3_5 44 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 61 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 216
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 216 (accept_3_5 41 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 216 (Polychromatic418967fa.accept_13_1_9_8_1_1734 40 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 216 (accept_3_5 38 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 61 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 216 (accept_3_5 35 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 34 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 216 (Polychromatic418967fa.accept_13_7_9_8_1_188 33 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 216 (accept_3_5 32 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 216 (Polychromatic418967fa.accept_19_12_4_7_1_4459 31 61 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 216
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 30 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 216 (accept_3_5 29 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 216 (Polychromatic418967fa.accept_16_12_13_8_1_2409 28 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 216 (accept_3_5 26 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 61 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 216
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 24 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 216 (accept_3_5 23 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 216 (Polychromatic418967fa.accept_16_5_13_8_1_2454 21 61 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 216 (accept_3_5 20 61 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 216 (Polychromatic418967fa.accept_16_3_13_8_1_1594 19 61
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 216 (accept_3_5 17 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 216 (Polychromatic418967fa.accept_13_3_9_8_1_4202 16 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 216 (accept_3_5 14 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 216 (Polychromatic418967fa.accept_14_13_5_6_1_2747 13 61 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 216
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 216 (accept_3_5 11 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 216 (Polychromatic418967fa.accept_15_10_1_6_1_3033 10 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 216 (Polychromatic418967fa.accept_15_9_1_6_1_657 9 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 216 (accept_3_5 8 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 61 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 216
  (Polychromatic418967fa.accept_17_6_10_12_1_4129 6 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 216 (accept_3_5 5 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  216 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 61 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 216 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 61 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 216 (accept_3_5 2 61 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 216 (allA_succ_of_accept 59 60 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 60 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 216 2 29 30 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 60 216 3 19 20 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 60 216 4 14 15 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 216
  (Polychromatic418967fa.accept_16_7_12_8_1_2450 55 60 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 60 216 6 9 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 60 216 (Polychromatic418967fa.accept_11_9_5_7_1_815 53 60 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 216 4 13 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 60 216 3 17 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 60 216 2 25 30 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 216
  (Polychromatic418967fa.accept_16_1_12_8_1_2405 49 60 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 216 12 4 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 60 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 216 2 23 30 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 216 3 15 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 216 4 11 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 216 (Polychromatic418967fa.accept_16_11_12_8_1_1592
  43 60 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 216 6 7 10 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 216
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 41 60 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 216 4 10 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 60 216 3 13 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 60 216 2 19 30 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 60 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 60 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 216 12 3 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 216 (Polychromatic418967fa.accept_16_3_12_8_1_808
  35 60 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 216 2 17 30 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 60 216 3 11 20 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 60 216 4 8 15 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 60 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 216 6 5 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 216 (Polychromatic418967fa.accept_16_13_12_8_1_2451 29 60 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 216 4 7 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 216 3 9 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 60 216 2 13 30 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 216 (Polychromatic418967fa.accept_16_9_12_8_1_1554
  25 60 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 216 12 2 5 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 216 2 11 30 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 60 216 3 7 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 60 216 4 5 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 60 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 60 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 216 6 3 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  60 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 216 4 4 15 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 216 3 5 20 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 216 2 7 30 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 216
  (Polychromatic418967fa.accept_16_13_12_8_1_2451 13 60 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 216 12 1 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 216 (Polychromatic418967fa.accept_16_11_12_8_1_1592 11 60 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 216 2 5 30 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 216 3 3 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 60 216 4 2 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 216 (Polychromatic418967fa.accept_16_7_12_8_1_2450 7
  60 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 216 6 1 10 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 60 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 216 4 1 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 60 216 3 1 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 60 216 2 1 30 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 216 (Polychromatic418967fa.accept_16_1_12_8_1_2405 1 60 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 216 (allA_succ_of_accept 58 59 216 (accept_3_4 58 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 59 216 (Polychromatic418967fa.accept_20_17_19_16_1_6996 57 59 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 59 216 (Polychromatic418967fa.accept_17_5_8_12_1_6609 56 59
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 216 (accept_3_4 55 59 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 216 (Polychromatic418967fa.accept_13_2_7_8_1_4221
  54 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 216 (accept_3_4 52 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 216 (Polychromatic418967fa.accept_15_5_14_6_1_5120 50 59 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 216 (accept_3_4 49 59 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 216 (Polychromatic418967fa.accept_13_9_7_8_1_1122 48 59 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 216
  (Polychromatic418967fa.accept_11_3_4_7_1_114 47 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 216 (accept_3_4 46 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 59 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 216 (accept_3_4 43 59 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 216 (Polychromatic418967fa.accept_13_3_7_8_1_4192 42 59 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 216
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 41 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 216 (accept_3_4 40 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 216 (Polychromatic418967fa.accept_13_12_7_8_1_1104 38 59 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 216 (accept_3_4 37 59 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 216 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 59 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 35 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 216 (accept_3_4 34 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 59 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 216 (accept_3_4 31 59 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 59 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 216
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 29 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 216 (accept_3_4 28 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 216 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 216 (Polychromatic418967fa.accept_23_3_13_9_1_12732 26 59 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 216 (accept_3_4 25 59 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 216 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 59
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 216 (accept_3_4 22 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 216 (Polychromatic418967fa.accept_16_5_11_8_1_3431 21 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 216 (Polychromatic418967fa.accept_15_5_14_6_1_5120 20 59 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 216 (accept_3_4 19 59 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 59 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 216
  (Polychromatic418967fa.accept_19_17_2_7_1_11422 17 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 216 (accept_3_4 16 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 216 (Polychromatic418967fa.accept_11_3_4_7_1_114 14 59 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 216 (accept_3_4 13 59 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 216 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 59 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 216 (accept_3_4 10 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 216 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 59 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 216 (accept_3_4 7 59 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 216 (Polychromatic418967fa.accept_25_6_9_16_1_12731 6 59 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 5
  59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 216 (accept_3_4 4 59 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 3
  59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 216 (accept_3_4 1 59 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 216 (allA_succ_of_accept 57 58 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 216 2 28 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 58 216 (Polychromatic418967fa.accept_17_4_7_12_1_6556 55 58 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 216 2 27 29 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 216 (accept_3_5 53 58 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 216 2 26 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 216 (Polychromatic418967fa.accept_19_13_1_7_1_5906
  51 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 216 2 25 29 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 216
  (Polychromatic418967fa.accept_15_4_13_6_1_642 49 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 216 2 24 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 58 216 (accept_3_5 47 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 58 216 2 23 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 58 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 58 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 216 2 22 29 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 216 2 21 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 58 216 (accept_3_5 41 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 58 216 2 20 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 58 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 58 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 216 2 19 29 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 216
  (Polychromatic418967fa.accept_11_4_3_7_1_828 37 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 216 2 18 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 58 216 (accept_3_5 35 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 58 216 2 17 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 58 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 58 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 216 2 16 29 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 216 2 15 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 58 216 (accept_3_5 29 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 58 216 2 14 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 58 216 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 58 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 216 2 13 29 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 216 2 12 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 58 216 (accept_3_5 23 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 58 216 2 11 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 58 216 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 58 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 216 2 10 29 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 216
  (Polychromatic418967fa.accept_15_4_13_6_1_642 19 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 216 2 9 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 216 (accept_3_5 17 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  216 2 8 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 216 2 7 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 58 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 58 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 216 2 6 29 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 216 (accept_3_5 11 58 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 216 2 5 29 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 216
  (Polychromatic418967fa.accept_21_9_16_6_1_5134 9 58 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 216 2 4 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 216 (Polychromatic418967fa.accept_15_7_13_6_1_696 7 58 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 216 2 3 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 216 (accept_3_5 5 58 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 216 2 2 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 58 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 216 2 1 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 58
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 216 (allA_succ_of_accept 56 57 216
  (Polychromatic418967fa.accept_26_4_5_8_1_12730 56 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 216 (Polychromatic418967fa.accept_13_3_5_8_1_1099 55 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 216 3 18 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 53
  57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 216
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 52 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 216 3 17 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 216 (Polychromatic418967fa.accept_15_5_12_6_1_639 50 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 216 (Polychromatic418967fa.accept_13_10_5_8_1_2555 49 57
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 216 3 16 19 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 216 (Polychromatic418967fa.accept_20_6_17_16_1_8470 46 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 216 3 15 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 44
  57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 43 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 216 3 14 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 41 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 57 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 216 3 13 19 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 216
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 38 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 216 3 12 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 216 (Polychromatic418967fa.accept_14_7_1_6_1_3514
  35 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 216
  (Polychromatic418967fa.accept_21_13_15_6_1_3556 34 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 216 3 11 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 216 (Polychromatic418967fa.accept_15_2_12_6_1_3063 32 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 31 57 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 216 3 10 19 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 216
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 29 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 216 (Polychromatic418967fa.accept_16_12_9_8_1_2508 28 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 216 3 9 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 57 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 216
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 25 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 216 3 8 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 216 (Polychromatic418967fa.accept_15_7_12_6_1_1327 22 57
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 216 3 7 19 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 216
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 216 3 6 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 216 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 57 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 216 3 5 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 14 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 57 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 216 3 4 19 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 11 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 216 (Polychromatic418967fa.accept_13_10_5_8_1_2555 10 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 216 3 3 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 216 (Polychromatic418967fa.accept_21_8_15_6_1_8247 8 57 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 216
  (Polychromatic418967fa.accept_14_7_1_6_1_3514 7 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 216 3 2 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 216 (Polychromatic418967fa.accept_16_4_9_8_1_2509 4 57 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 216 3 1 19 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 57 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 57 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 216 (allA_succ_of_accept 55 56 216 (accept_3_4 55 56 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  54 56 216 2 27 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 216 (Polychromatic418967fa.accept_19_15_18_7_1_10018 53 56 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 216 4 13 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 216 (Polychromatic418967fa.accept_13_12_4_8_1_1120
  51 56 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 216 2 25 28 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 216
  (accept_3_4 49 56 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 216 8 6 7 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 216
  (Polychromatic418967fa.accept_15_2_11_6_1_2135 47 56 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 216 2 23 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 56 216 (Polychromatic418967fa.accept_21_3_14_6_1_11325 45 56 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 216 4 11 14 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 216 (accept_3_4 43 56 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 216 2 21 28 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 216
  (Polychromatic418967fa.accept_17_7_5_12_1_1997 41 56 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 56 216 8 5 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 56 216 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 56 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 216 2 19 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 216 (accept_3_4 37 56 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 216 4 9 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 56 216 (Polychromatic418967fa.accept_13_9_4_8_1_1752 35 56 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 216 2 17 28 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 216
  (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 56 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 216 8 4 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 216 (accept_3_4 31 56 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56
  216 2 15 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 56 216 (Polychromatic418967fa.accept_19_10_18_7_1_12729 29 56 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 216 4 7 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 56 216 (Polychromatic418967fa.accept_17_10_5_12_1_4101 27 56 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 216 2 13 28 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 216 (accept_3_4 25 56 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 216 8 3 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 216 (Polychromatic418967fa.accept_13_10_4_8_1_2570
  23 56 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 216 2 11 28 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 216
  (Polychromatic418967fa.accept_25_21_6_16_1_12728 21 56 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 56 216 4 5 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 56 216 (accept_3_4 19 56 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 56 216 2 9 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 56 216 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 56 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 216 8 2 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 216 (Polychromatic418967fa.accept_19_15_18_7_1_10018 15 56
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 216 2 7 28 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 216 (accept_3_4 13
  56 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 216 4 3 14 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 216
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 56 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 56 216 2 5 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 56 216 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 56 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 216 8 1 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 216 (accept_3_4 7 56 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 56 216 2 3 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 56 216 (Polychromatic418967fa.accept_15_5_11_6_1_692 5 56 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 216 4 1 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 216 (Polychromatic418967fa.accept_15_3_11_6_1_3083 3
  56 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 216 2 1 28 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 216 (accept_3_4 1 56
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 216 (allA_succ_of_accept 54 55 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 55 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 216 (accept_3_5 53 55 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 216 (Polychromatic418967fa.accept_16_4_7_8_1_5753 52 55 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 51 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 216 (accept_3_5 50 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 216 (Polychromatic418967fa.accept_13_9_3_8_1_573 48 55 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 216 (accept_3_5 47 55 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 46 55 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 216
  (Polychromatic418967fa.accept_20_5_15_16_1_12727 45 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 55 216 (accept_3_5 44 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 55 216 (Polychromatic418967fa.accept_17_9_4_12_1_2958 43 55 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 216 (Polychromatic418967fa.accept_15_12_10_6_1_2134 42 55
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 216 (accept_3_5 41 55 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 216
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 40 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 55 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 55 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 216 (accept_3_5 38 55 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 55 216 (Polychromatic418967fa.accept_13_11_3_8_1_1786 37 55 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 216
  (Polychromatic418967fa.accept_16_4_7_8_1_5753 36 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 216 (accept_3_5 35 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 33 55 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 216 (accept_3_5 32 55 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 55 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 216
  (Polychromatic418967fa.accept_20_10_15_16_1_6994 30 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 55 216 (accept_3_5 29 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 55 216 (Polychromatic418967fa.accept_16_12_7_8_1_1589 28 55 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 216 (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 55
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 216 (accept_3_5 26 55 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 216 (Polychromatic418967fa.accept_16_9_7_8_1_1588
  25 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 216
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 216 (accept_3_5 23 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 216 (Polychromatic418967fa.accept_13_9_3_8_1_573 22 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 55 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 216 (accept_3_5 20 55 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 55 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 216
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 216 (accept_3_5 17 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 216 (Polychromatic418967fa.accept_15_1_10_6_1_631 16 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 216 (Polychromatic418967fa.accept_16_15_7_8_1_8189 15 55 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 216 (accept_3_5 14 55 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 216 (Polychromatic418967fa.accept_19_13_17_7_1_12726 13 55
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 216
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 216 (accept_3_5 11 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 216 (Polychromatic418967fa.accept_19_10_17_7_1_12725 10 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 55 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 216 (accept_3_5 8 55 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 55 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 216
  (Polychromatic418967fa.accept_22_6_11_18_1_11255 6 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 216 (accept_3_5 5 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  216 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 55 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 216 (Polychromatic418967fa.accept_15_3_10_6_1_632 3 55 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 216 (accept_3_5 2 55 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 55 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 216 (allA_succ_of_accept 53 54 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 54 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 216 2 26 27 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 54 216 3 17 18 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 54 216 2 25 27 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 216
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 49 54 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 216 6 8 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 216 (Polychromatic418967fa.accept_11_3_10_7_1_129 47 54 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 216 2 23 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 54 216 9 5 6 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 54 216 2 22 27 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 54 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 216 6 7 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 216 (Polychromatic418967fa.accept_14_13_12_6_1_2735 41 54 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 216 2 20 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 54 216 3 13 18 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 54 216 2 19 27 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 216
  (Polychromatic418967fa.accept_21_16_12_6_1_8274 37 54 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 216 18 2 3 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 54 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 54 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 216 2 17 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 54 216 3 11 18 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 54 216 2 16 27 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 216
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 31 54 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 216 6 5 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 54 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 216 2 14 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 54 216 27 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 54 216 2 13 27 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 54 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 216 6 4 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 216 (Polychromatic418967fa.accept_13_10_2_8_1_2603 23 54 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 216 2 11 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 54 216 3 7 18 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 54 216 2 10 27 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 216
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 54 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 216 18 1 3 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 216 (Polychromatic418967fa.accept_19_17_16_7_1_7213 17 54 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 216 2 8 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 54 216 3 5 18 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 54 216 2 7 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 216 (Polychromatic418967fa.accept_14_13_12_6_1_2735
  13 54 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 216 6 2 9 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 54 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 216 2 5 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 54 216 9 1 6 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 54 216 2 4 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 216 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 54 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 216 6 1 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 54 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 216 2 2 27 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 54 216 3 1 18 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 54 216 2 1 27 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 54 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 216)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 216 (allA_succ_of_accept 52 53
  216 (accept_3_4 52 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 216 (Polychromatic418967fa.accept_13_11_1_8_1_1776 50 53 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 216 (accept_3_4 49 53 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 53 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 216 (accept_3_4 46 53
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 53 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 216 (accept_3_4 43 53 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 216 (Polychromatic418967fa.accept_22_20_9_18_1_8087 42 53 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 216
  (Polychromatic418967fa.accept_17_7_2_12_1_1069 41 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 216 (accept_3_4 40 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 53 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 216 (accept_3_4 37 53 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 216 (Polychromatic418967fa.accept_16_4_5_8_1_2425 36 53 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 216
  (Polychromatic418967fa.accept_11_2_9_7_1_124 35 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 216 (accept_3_4 34 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 216 (Polychromatic418967fa.accept_13_6_1_8_1_1116 32 53 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 216 (accept_3_4 31 53 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 53 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 216
  (Polychromatic418967fa.accept_10_9_3_6_1_686 29 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 216 (accept_3_4 28 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 53 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 216 (accept_3_4 25 53 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 216 (accept_3_4 22 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 216 (Polychromatic418967fa.accept_17_4_2_12_1_6554 21 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 216 (Polychromatic418967fa.accept_13_7_1_8_1_1778 20 53 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 216 (accept_3_4 19 53 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 53 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 216 (accept_3_4 16 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 216 (Polychromatic418967fa.accept_21_15_11_6_1_5121 15 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 216 (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 53 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 216 (accept_3_4 13 53 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 216
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 216 (accept_3_4 10 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 53 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 216 (accept_3_4 7 53 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 216 (Polychromatic418967fa.accept_13_6_1_8_1_1116 6 53 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 216 (accept_3_4 4 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  216 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 53 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 53 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 216 (accept_3_4 1 53 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 216))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 216
  (allA_succ_of_accept 51 52 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 52 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 216 2 25 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 216 (Polychromatic418967fa.accept_16_1_4_8_1_3434
  49 52 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 216 4 12 13 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 216 (accept_3_5 47
  52 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 216 2 23 26 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 216
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 52 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 52 216 4 11 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 52 216 (Polychromatic418967fa.accept_15_13_7_6_1_682 43 52 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 216 2 21 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 216 (accept_3_5 41 52 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 216 4 10 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 52 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 216 2 19 26 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 52 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 216 4 9 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 52 216 (accept_3_5 35 52 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52
  216 2 17 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 52 216 (Polychromatic418967fa.accept_16_1_4_8_1_3434 33 52 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 52 216 4 8 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 52 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 52 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 216 2 15 26 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 216 (accept_3_5 29 52 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 216 4 7 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 216 (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 52 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 216 2 13 26 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 52 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 216 4 6 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 52 216 (accept_3_5 23 52 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52
  216 2 11 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 52 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 52 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 52 216 4 5 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 52 216 (Polychromatic418967fa.accept_16_3_4_8_1_3450 19 52 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 216 2 9 26 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 216 (accept_3_5 17 52 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 216 4 4 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52 216 (Polychromatic418967fa.accept_11_4_8_7_1_819 15 52 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 216 2 7 26 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 216
  (Polychromatic418967fa.accept_15_13_7_6_1_682 13 52 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 216 4 3 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 216 (accept_3_5 11 52 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  216 2 5 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 52 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 52 216 4 2 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 52 216 (Polychromatic418967fa.accept_16_7_4_8_1_2487 7 52 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 216 2 3 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 216 (accept_3_5 5 52 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 52 216 4 1 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 52 216 (Polychromatic418967fa.accept_14_3_10_6_1_1136 3 52 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 216 2 1 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 1
  52 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  216)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 216 (allA_succ_of_accept 50 51 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 216 (Polychromatic418967fa.accept_13_10_12_8_1_2550 49 51 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 216 3 16 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 47
  51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 46 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 216 3 15 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 216 (Polychromatic418967fa.accept_13_5_12_8_1_198 44 51 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 51 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 216 3 14 17 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 216
  (Polychromatic418967fa.accept_19_3_13_7_1_7245 41 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 216 (Polychromatic418967fa.accept_13_1_12_8_1_1818 40 51 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 216 3 13 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 38
  51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 216
  (Polychromatic418967fa.accept_10_7_1_6_1_673 37 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 216 3 12 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 35 51 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 216 (Polychromatic418967fa.accept_19_15_13_7_1_7246 34 51
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 216 3 11 17 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 51 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 216 3 10 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 29
  51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 216
  (Polychromatic418967fa.accept_16_12_3_8_1_5729 28 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 216 3 9 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 216 (Polychromatic418967fa.accept_20_6_11_16_1_3992 26 51 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 51 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 216 3 8 17 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 216
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 23 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 51 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 216 3 7 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 216 (Polychromatic418967fa.accept_13_7_12_8_1_199 20 51 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 216
  (Polychromatic418967fa.accept_22_19_7_18_1_12724 19 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 51 216 3 6 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 51 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 51 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 216 (Polychromatic418967fa.accept_21_16_9_6_1_8335
  16 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 216 3 5 17 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 216
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 14 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 216 (Polychromatic418967fa.accept_16_13_3_8_1_2422 13 51 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 216 3 4 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 51 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 216 3 3 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 51 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 51 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 216 3 2 17 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 216
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 51 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 216 3 1 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 51 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 51 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 216))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 216 (allA_succ_of_accept 49 50 216
  (accept_3_4 49 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 216 2 24 25 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 216 2 23 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 50 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 50 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 216 2 22 25 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 216 (accept_3_4 43 50 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 216 2 21 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 216 (Polychromatic418967fa.accept_15_11_5_6_1_669
  41 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 216 2 20 25 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 216
  (Polychromatic418967fa.accept_19_1_12_7_1_12723 39 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 216 2 19 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 50 216 (accept_3_4 37 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 50 216 2 18 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 50 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 50 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 216 2 17 25 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 216 2 16 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 50 216 (accept_3_4 31 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 50 216 2 15 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 216 (Polychromatic418967fa.accept_13_3_11_8_1_1094 29 50 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 216 2 14 25 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 216
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 50 216 2 13 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 50 216 (accept_3_4 25 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 50 216 2 12 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 50 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 216 2 11 25 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 216
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 216 2 10 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 216 (accept_3_4 19 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 50 216 2 9 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 50 216 (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 50 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 216 2 8 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 216 (Polychromatic418967fa.accept_19_15_12_7_1_7227
  15 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 216 2 7 25 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 216 (accept_3_4 13
  50 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 216 2 6 25 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 216
  (Polychromatic418967fa.accept_15_11_5_6_1_669 11 50 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 216 2 5 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 50 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 216 2 4 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 216 (accept_3_4 7 50 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 216 2 3 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 50 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 216 2 2 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 216 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3
  50 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 216 2 1 25 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 216 (accept_3_4 1 50
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 216))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 216 (allA_succ_of_accept 48 49 216 (Polychromatic418967fa.accept_17_14_15_12_1_1921 48 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 216 (accept_3_5 47 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 216 (Polychromatic418967fa.accept_13_7_10_8_1_567 46 49 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 45 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 216 (accept_3_5 44 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 43 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 216 (Polychromatic418967fa.accept_11_9_5_7_1_815 42 49 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 216 (accept_3_5 41 49 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 216 (Polychromatic418967fa.accept_15_10_4_6_1_2129 40 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 216
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 39 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 216 (accept_3_5 38 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 216 (Polychromatic418967fa.accept_13_11_10_8_1_1804 37 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 216 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 49 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 216 (accept_3_5 35 49 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 216 (Polychromatic418967fa.accept_19_15_11_7_1_8711 34 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 216
  (Polychromatic418967fa.accept_10_3_9_6_1_94 33 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 216 (accept_3_5 32 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 216 (Polychromatic418967fa.accept_11_9_5_7_1_815 31 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 216 (Polychromatic418967fa.accept_13_4_10_8_1_1817 30 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 216 (accept_3_5 29 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 216 (Polychromatic418967fa.accept_13_2_10_8_1_1126 28 49
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 216
  (Polychromatic418967fa.accept_14_13_7_6_1_3525 27 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 216 (accept_3_5 26 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 216 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 216 (accept_3_5 23 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 216 (Polychromatic418967fa.accept_14_8_7_6_1_1159 22 49 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 216
  (Polychromatic418967fa.accept_26_21_23_8_1_5203 21 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 216 (accept_3_5 20 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 216 (Polychromatic418967fa.accept_20_19_9_16_1_2744 19 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 216 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 216 (accept_3_5 17 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 216 (Polychromatic418967fa.accept_21_16_7_6_1_6687 16 49
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 15 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 216 (accept_3_5 14 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 216 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 216 (accept_3_5 11 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 216 (Polychromatic418967fa.accept_15_10_4_6_1_2129 10 49
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 216
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 216 (accept_3_5 8 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  216 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 216 (Polychromatic418967fa.accept_23_6_3_9_1_12722 6 49 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 216 (accept_3_5 5 49 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 216 (Polychromatic418967fa.accept_13_4_10_8_1_1817 4 49 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 216
  (Polychromatic418967fa.accept_10_3_9_6_1_94 3 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 216 (accept_3_5 2 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  216 (Polychromatic418967fa.accept_14_1_7_6_1_3604 1 49 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 49 216))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 216 (allA_succ_of_accept
  47 48 216 (Polychromatic418967fa.accept_11_3_4_7_1_114 47 48 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 48 216 2 23 24 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 48 216 3 15 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 48 216 4 11 12 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 48 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 43 48 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 216 6 7 8 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 216
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 41 48 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 216 8 5 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 48 216 3 13 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 48 216 2 19 24 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 48 216 (Polychromatic418967fa.accept_13_11_9_8_1_1125 37 48 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 216 12 3 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 216 (Polychromatic418967fa.accept_15_5_3_6_1_2128
  35 48 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 216 2 17 24 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 48 216 3 11 16 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 48 216 8 4 6 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 216
  (Polychromatic418967fa.accept_15_1_3_6_1_621 31 48 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 216 6 5 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 216 (Polychromatic418967fa.accept_13_3_9_8_1_4202 29 48 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 216 4 7 12 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 48 216 3 9 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 48 216 2 13 24 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 216 (Polychromatic418967fa.accept_11_3_4_7_1_114 25
  48 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 216 24 1 2 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 23 48 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 48 216 2 11 24 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 48 216 3 7 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 48 216 4 5 12 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 216 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 48 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 216 6 3 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 216 (Polychromatic418967fa.accept_13_4_9_8_1_1736
  17 48 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 216 8 2 6 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 216 3 5 16 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 48 216 2 7 24 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 48 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 216 12 1 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 216 (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 48 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 216 2 5 24 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 48 216 3 3 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 48 216 8 1 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 216 (Polychromatic418967fa.accept_13_7_9_8_1_188 7
  48 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 216 6 1 8 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 216
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 48 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 216 4 1 12 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 48 216 3 1 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 48 216 2 1 24 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 216 (Polychromatic418967fa.accept_13_1_9_8_1_1734 1 48 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 216)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 216
  (allA_succ_of_accept 46 47 216 (accept_3_4 46 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 216 (Polychromatic418967fa.accept_17_11_13_12_1_1968 45 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 216 (Polychromatic418967fa.accept_16_12_15_8_1_4586 44 47 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 216 (accept_3_4 43 47 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 216 (Polychromatic418967fa.accept_15_12_2_6_1_2127 42 47
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 41 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 216 (accept_3_4 40 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 216 (Polychromatic418967fa.accept_15_8_2_6_1_2125 38 47 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 216 (accept_3_4 37 47 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 216
  (Polychromatic418967fa.accept_17_1_13_12_1_1084 35 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 216 (accept_3_4 34 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 47 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 216 (accept_3_4 31 47 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 216 (Polychromatic418967fa.accept_19_11_9_7_1_4447 30 47 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 216 (accept_3_4 28 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 216 (Polychromatic418967fa.accept_14_13_5_6_1_2747 27 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 216 (Polychromatic418967fa.accept_11_4_3_7_1_828 26 47 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 216 (accept_3_4 25 47 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 216 (Polychromatic418967fa.accept_19_5_9_7_1_3137 24 47 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 23 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 216 (accept_3_4 22 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 216 (Polychromatic418967fa.accept_16_4_15_8_1_2413 20 47 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 216 (accept_3_4 19 47 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 47 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 216
  (Polychromatic418967fa.accept_16_1_15_8_1_2411 17 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 216 (accept_3_4 16 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 216 (Polychromatic418967fa.accept_23_14_1_9_1_12721 14 47 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 216 (accept_3_4 13 47 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 216 (Polychromatic418967fa.accept_15_12_2_6_1_2127 12 47
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 216 (accept_3_4 10 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 216 (Polychromatic418967fa.accept_16_9_15_8_1_3425 9 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 47 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 216 (accept_3_4 7 47 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 216 (Polychromatic418967fa.accept_20_6_7_16_1_5437 6 47 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 216
  (Polychromatic418967fa.accept_19_5_9_7_1_3137 5 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 216 (accept_3_4 4 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  216 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 47 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 216 (Polychromatic418967fa.accept_19_2_9_7_1_11483 2 47 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 216 (accept_3_4 1 47 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 216))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 216 (allA_succ_of_accept 45
  46 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 46 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 46 216 2 22 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 46 216 (Polychromatic418967fa.accept_25_18_21_16_1_12720 43 46 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 216 2 21 23 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 216 (accept_3_5 41
  46 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 216 2 20 23 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 216
  (Polychromatic418967fa.accept_15_9_1_6_1_657 39 46 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 46 216 2 19 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 46 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 46 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 216 2 18 23 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 216 (accept_3_5 35 46 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 216 2 17 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 33
  46 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 216 2 16 23 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 46 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 216 2 15 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 46 216 (accept_3_5 29 46 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 46 216 2 14 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 216 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 46 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 216 2 13 23 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 216
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 25 46 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 46 216 2 12 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 46 216 (accept_3_5 23 46 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 46 216 2 11 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 46 216 (Polychromatic418967fa.accept_20_1_6_16_1_6991 21 46 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 216 2 10 23 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 46 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 216 2 9 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 216 (accept_3_5 17 46 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  216 2 8 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 216 (Polychromatic418967fa.accept_13_2_7_8_1_4221 15 46 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 216 2 7 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 46 216 (Polychromatic418967fa.accept_21_13_4_6_1_6668 13 46 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 216 2 6 23 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 216 (accept_3_5 11 46 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 216 2 5 23 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 46 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 216 2 4 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 216 (Polychromatic418967fa.accept_15_7_1_6_1_6150 7 46 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 216 2 3 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 216 (accept_3_5 5 46 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 216 2 2 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 46 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 216 2 1 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 216 (Polychromatic418967fa.accept_13_1_7_8_1_1796 1
  46 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  216)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 216 (allA_succ_of_accept 44 45 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 216 (Polychromatic418967fa.accept_16_11_13_8_1_1578 43 45 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 216 3 14 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 41
  45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 216
  (Polychromatic418967fa.accept_13_1_6_8_1_208 40 45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 216 3 13 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 216 (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 45 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 45 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 216 9 4 5 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 216
  (Polychromatic418967fa.accept_16_3_13_8_1_1594 35 45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 45 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 216 3 11 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 32
  45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 31 45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 216 3 10 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 29 45 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 216 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 45 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 216 9 3 5 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 216
  (Polychromatic418967fa.accept_21_5_3_6_1_6648 26 45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 45 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 216 3 8 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 45 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 216
  (Polychromatic418967fa.accept_21_1_3_6_1_8321 22 45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 216 3 7 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 216 (Polychromatic418967fa.accept_16_4_13_8_1_3424 20 45 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 45 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 216 9 2 5 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 216
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 45 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 216 3 5 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 45 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 216
  (Polychromatic418967fa.accept_17_13_11_12_1_4131 13 45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 45 216 3 4 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 45 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 45 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 216 (Polychromatic418967fa.accept_14_10_3_6_1_2728
  10 45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 216 9 1 5 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 216
  (Polychromatic418967fa.accept_21_8_3_6_1_11279 8 45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 216 (Polychromatic418967fa.accept_21_7_3_6_1_8322 7 45 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 216 3 2 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 216 (Polychromatic418967fa.accept_16_5_13_8_1_2454 5 45 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 45 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 216 3 1 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 45 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 45 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  216))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 216 (allA_succ_of_accept 43 44 216 (accept_3_4 43 44
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 216 2 21 22 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 216
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 41 44 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 216 4 10 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 44 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 216 2 19 22 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 216 (accept_3_4 37 44 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 216 4 9 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 44 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 44 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 216 2 17 22 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 216
  (Polychromatic418967fa.accept_16_1_12_8_1_2405 33 44 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 216 4 8 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 216 (accept_3_4 31 44 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  216 2 15 22 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 44 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 44 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 216 4 7 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 44 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 44 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 216 2 13 22 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 216 (accept_3_4 25 44 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 216 4 6 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 216 (Polychromatic418967fa.accept_13_10_5_8_1_2555 23 44 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 216 2 11 22 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 216
  (Polychromatic418967fa.accept_16_5_12_8_1_2521 21 44 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 216 4 5 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 216 (accept_3_4 19 44 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  216 2 9 22 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 44 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 216 4 4 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 44 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 216 2 7 22 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 216 (accept_3_4 13 44 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 216 4 3 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 44 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 216 2 5 22 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 216
  (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 44 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 216 4 2 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 216 (accept_3_4 7 44 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 216
  2 3 22 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  216 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 44 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 216 4 1 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 44 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 216 2 1 22 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 216 (accept_3_4 1 44 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 216)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 216 (allA_succ_of_accept 42 43
  216 (Polychromatic418967fa.accept_25_17_18_16_1_12719 42 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 43 216 (accept_3_5 41 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 43 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 43 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 43 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 216 (accept_3_5 38 43 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 37
  43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 216
  (Polychromatic418967fa.accept_11_3_10_7_1_129 36 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 216 (accept_3_5 35 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 216 (Polychromatic418967fa.accept_15_4_13_6_1_642 34 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 43 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 216 (accept_3_5 32 43 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 216 (Polychromatic418967fa.accept_17_14_9_12_1_5350 31 43 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 216 (accept_3_5 29 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 43 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 216 (accept_3_5 26 43 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 216 (Polychromatic418967fa.accept_11_3_10_7_1_129 25 43 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 216
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 24 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 216 (accept_3_5 23 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 216 (Polychromatic418967fa.accept_13_9_4_8_1_1752 22 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 216 (Polychromatic418967fa.accept_14_7_1_6_1_3514 21 43 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 216 (accept_3_5 20 43 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 43 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 216
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 216 (accept_3_5 17 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 216 (Polychromatic418967fa.accept_21_15_1_6_1_8258 15 43 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 216 (accept_3_5 14 43 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 216 (Polychromatic418967fa.accept_16_13_11_8_1_2449 13 43
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 216 (accept_3_5 11 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 216 (Polychromatic418967fa.accept_13_10_4_8_1_2570 10 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 43 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 216 (accept_3_5 8 43 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 43 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 216
  (Polychromatic418967fa.accept_19_6_5_7_1_8708 6 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 216 (accept_3_5 5 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  216 (Polychromatic418967fa.accept_15_4_13_6_1_642 4 43 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 216 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 43 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 216 (accept_3_5 2 43 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 216 (Polychromatic418967fa.accept_28_1_15_20_1_12718 1 43 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 216)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 216 (allA_succ_of_accept 41 42 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 42 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 216 2 20 21 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 42 216 3 13 14 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 42 216 2 19 21 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 216
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 37 42 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 216 6 6 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 216 (Polychromatic418967fa.accept_11_2_9_7_1_124 35 42 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 216 2 17 21 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 42 216 3 11 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 42 216 2 16 21 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 42 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 216 6 5 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 216 (Polychromatic418967fa.accept_23_6_19_9_1_12717 29 42 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 216 2 14 21 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 216 3 9 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 216 2 13 21 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 216
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 42 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 216 6 4 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 216 (Polychromatic418967fa.accept_22_1_20_18_1_8080 23 42 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 216 2 11 21 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 216 3 7 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 216 2 10 21 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 216
  (Polychromatic418967fa.accept_25_19_17_16_1_12716 19 42 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 42 216 6 3 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 42 216 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 42 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 216 2 8 21 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 42 216 3 5 14 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 42 216 2 7 21 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 216
  (Polychromatic418967fa.accept_11_2_9_7_1_124 13 42 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 42 216 6 2 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 42 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 42 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 216 2 5 21 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 216 3 3 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 216 2 4 21 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7
  42 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 216 6 1 7 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 216
  (Polychromatic418967fa.accept_11_5_9_7_1_411 5 42 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 216 2 2 21 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 42 216 3 1 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 42 216 2 1 21 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 42 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 216)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 216
  (allA_succ_of_accept 40 41 216 (accept_3_4 40 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 216 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 216 (Polychromatic418967fa.accept_17_4_7_12_1_6556 38 41 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 216 (accept_3_4 37 41 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 216 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 41
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 216
  (Polychromatic418967fa.accept_10_5_1_6_1_672 35 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 216 (accept_3_4 34 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 216 (Polychromatic418967fa.accept_13_7_2_8_1_1746 33 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 32 41 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 216 (accept_3_4 31 41 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 216 (Polychromatic418967fa.accept_21_9_20_6_1_9815 30 41 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 216
  (Polychromatic418967fa.accept_19_10_3_7_1_12715 29 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 216 (accept_3_4 28 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 216 (Polychromatic418967fa.accept_11_4_8_7_1_819 26 41 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 216 (accept_3_4 25 41 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 216 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 41 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 216
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 23 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 216 (accept_3_4 22 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 216 (Polychromatic418967fa.accept_14_7_13_6_1_1177 21 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 216 (Polychromatic418967fa.accept_13_7_2_8_1_1746 20 41 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 216 (accept_3_4 19 41 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 216 (Polychromatic418967fa.accept_15_3_11_6_1_3083 18 41 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 216
  (Polychromatic418967fa.accept_10_7_1_6_1_673 17 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 216 (accept_3_4 16 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 216 (Polychromatic418967fa.accept_19_14_3_7_1_7248 14 41 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 216 (accept_3_4 13 41 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 41 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 216
  (Polychromatic418967fa.accept_20_11_1_16_1_8513 11 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 216 (accept_3_4 10 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 216 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 216 (Polychromatic418967fa.accept_22_8_19_18_1_12714 8 41 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 216 (accept_3_4 7 41 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 216 (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 41 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 216
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 216 (accept_3_4 4 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  216 (Polychromatic418967fa.accept_15_3_11_6_1_3083 3 41 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 41 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 41 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 216 (accept_3_4 1 41 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 41 216))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 216 (allA_succ_of_accept
  39 40 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 40 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 40 216 2 19 20 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 40 216 (Polychromatic418967fa.accept_13_11_1_8_1_1776 37 40 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 216 4 9 10 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 216 (accept_3_5 35 40 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 216 2 17 20 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 216 (Polychromatic418967fa.accept_13_7_1_8_1_1778
  33 40 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 216 8 4 5 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 216
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 31 40 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 216 2 15 20 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 40 216 (accept_3_5 29 40 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 40 216 4 7 10 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 40 216 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 40 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 216 2 13 20 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 25
  40 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 216 8 3 5 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 216 (accept_3_5 23
  40 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 216 2 11 20 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 216
  (Polychromatic418967fa.accept_26_21_14_8_1_12713 21 40 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 40 216 4 5 10 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 40 216 (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 40 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 216 2 9 20 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 216 (accept_3_5 17 40 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 216 8 2 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 40 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 40 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 216 2 7 20 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 216
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 40 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 40 216 4 3 10 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 40 216 (accept_3_5 11 40 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  216 2 5 20 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  40 216 (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 40 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 40 216 8 1 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 40 216 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 40 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 216 2 3 20 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 216 (accept_3_5 5 40 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 216 4 1 10 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 40 216 (Polychromatic418967fa.accept_15_3_10_6_1_632 3 40 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 216 2 1 20 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 40 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 216)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 216 (allA_succ_of_accept 38 39 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 39 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 39 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 216 3 12 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 35
  39 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 216
  (Polychromatic418967fa.accept_11_1_6_7_1_116 34 39 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 216 3 11 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 216 (Polychromatic418967fa.accept_19_13_1_7_1_5906 32 39 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 39 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 216 3 10 13 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 216
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 29 39 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 216 (Polychromatic418967fa.accept_16_12_7_8_1_1589 28 39 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 216 3 9 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 39 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 25 39 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 216 3 8 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 39 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 216 (Polychromatic418967fa.accept_28_22_11_20_1_12712 22 39
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 216 3 7 13 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 216
  (Polychromatic418967fa.accept_16_4_7_8_1_5753 20 39 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 39 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 216 3 6 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 39 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 39 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 216 3 5 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 216 (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 39 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 39 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 216 3 4 13 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 216
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 39 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 39 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 216 3 3 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 216 (Polychromatic418967fa.accept_17_8_5_12_1_7925 8 39 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 216
  (Polychromatic418967fa.accept_17_7_5_12_1_1997 7 39 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 216 3 2 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 39 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 216 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 39 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 216 3 1 13 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 39 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 39 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 216))))))))))))))))))))))))))))))))))))))) (allB_succ 38 216
  (allA_succ_of_accept 37 38 216 (accept_3_4 37 38 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  216 2 18 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 38 216 (Polychromatic418967fa.accept_13_9_12_8_1_570 35 38 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 216 2 17 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 38 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 216 2 16 19 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 216 (accept_3_4 31 38 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 216 2 15 19 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 216
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 29 38 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 216 2 14 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 38 216 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 38 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 216 2 13 19 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 216 (accept_3_4 25 38 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 216 2 12 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 38
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 216 2 11 19 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 216
  (Polychromatic418967fa.accept_20_1_18_16_1_12711 21 38 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 38 216 2 10 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 38 216 (accept_3_4 19 38 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 38 216 2 9 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 38 216 (Polychromatic418967fa.accept_13_4_12_8_1_197 17 38 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 216 2 8 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 216
  (Polychromatic418967fa.accept_20_15_18_16_1_5441 15 38 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 38 216 2 7 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 38 216 (accept_3_4 13 38 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 38 216 2 6 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 38 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 38 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 216 2 5 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 38
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 216 2 4 19 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 216 (accept_3_4 7 38
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 216 2 3 19 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38 216
  (Polychromatic418967fa.accept_13_5_12_8_1_198 5 38 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 216 2 2 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 38 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 216 2 1 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 216 (accept_3_4 1 38 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 216)))))))))))))))))))))))))))))))))))))) (allB_succ 37 216 (allA_succ_of_accept 36 37 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 216 (accept_3_5 35 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 216 (Polychromatic418967fa.accept_19_15_18_7_1_10018 34 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 37 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 216 (accept_3_5 32 37 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 37 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 216
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 216 (accept_3_5 29 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 216 (Polychromatic418967fa.accept_15_13_7_6_1_682 28 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 216 (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 37 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 216 (accept_3_5 26 37 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 37 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 216 (accept_3_5 23 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 37 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 216 (accept_3_5 20 37 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 216 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 37 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 216 (accept_3_5 17 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 216 (Polychromatic418967fa.accept_13_3_11_8_1_1094 16 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 37 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 216 (accept_3_5 14 37 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 37 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 216
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 12 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 216 (accept_3_5 11 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 37 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 216 (accept_3_5 8 37 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 216 (Polychromatic418967fa.accept_17_7_3_12_1_4098 7 37 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 216
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 6 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 216 (accept_3_5 5 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  216 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 37 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 37 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 216 (accept_3_5 2 37 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 216))))))))))))))))))))))))))))))))))))) (allB_succ 36 216
  (allA_succ_of_accept 35 36 216 (Polychromatic418967fa.accept_14_7_8_6_1_1164 35 36 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 216 2 17 18 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 216 3 11 12 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 216 4 8 9 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 216 (Polychromatic418967fa.accept_13_5_10_8_1_1127
  31 36 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 216 6 5 6 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 216
  (Polychromatic418967fa.accept_16_13_4_8_1_4557 29 36 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 36 216 4 7 9 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 36 216 9 3 4 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 36 216 2 13 18 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 36 216 (Polychromatic418967fa.accept_13_12_10_8_1_3343 25 36 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 216 12 2 3 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 36 216 2 11 18 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 36 216 3 7 12 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 36 216 4 5 9 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 36 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 216 18 1 2 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 216 (Polychromatic418967fa.accept_13_4_10_8_1_1817
  17 36 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 216 4 4 9 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 216 3 5 12 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 216 2 7 18 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 216
  (Polychromatic418967fa.accept_16_13_4_8_1_4557 13 36 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 216 12 1 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 216 (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 36 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 216 2 5 18 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 36 216 9 1 4 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 36 216 4 2 9 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 216 (Polychromatic418967fa.accept_13_7_10_8_1_567 7
  36 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 216 6 1 6 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 36 216 4 1 9 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 36 216 3 1 12 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 36 216 2 1 18 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 216 (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 36 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 216)))))))))))))))))))))))))))))))))))) (allB_succ 35 216
  (allA_succ_of_accept 34 35 216 (accept_3_4 34 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  35 216 (Polychromatic418967fa.accept_13_7_9_8_1_188 33 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 216 (Polychromatic418967fa.accept_17_15_1_12_1_7910 32 35 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 216 (accept_3_4 31 35 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 216 (Polychromatic418967fa.accept_13_4_9_8_1_1736 30 35 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 216
  (Polychromatic418967fa.accept_10_9_5_6_1_691 29 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 216 (accept_3_4 28 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 216 (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 216 (Polychromatic418967fa.accept_15_11_5_6_1_669 26 35 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 216 (accept_3_4 25 35 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 35 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 216
  (Polychromatic418967fa.accept_17_6_1_12_1_4115 23 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 216 (accept_3_4 22 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 216 (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 35 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 216 (accept_3_4 19 35 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 216 (Polychromatic418967fa.accept_15_3_5_6_1_4005 18 35 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 216
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 17 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 216 (accept_3_4 16 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 216 (Polychromatic418967fa.accept_14_1_7_6_1_3604 15 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 35 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 216 (accept_3_4 13 35 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 216 (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 35 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 11 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 216 (accept_3_4 10 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 216 (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 35 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 216 (accept_3_4 7 35 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 216 (Polychromatic418967fa.accept_17_6_1_12_1_4115 6 35 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 216
  (Polychromatic418967fa.accept_16_5_3_8_1_4555 5 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 216 (accept_3_4 4 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  216 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 35 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 35 216 (Polychromatic418967fa.accept_19_2_16_7_1_11424 2 35 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 216 (accept_3_4 1 35 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 35 216))))))))))))))))))))))))))))))))))) (allB_succ 34 216 (allA_succ_of_accept 33 34
  216 (Polychromatic418967fa.accept_19_14_15_7_1_7205 33 34 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 34 216 2 16 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 34 216 (Polychromatic418967fa.accept_19_12_15_7_1_11432 31 34 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 216 2 15 17 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 216 (accept_3_5 29 34 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 216 2 14 17 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 216
  (Polychromatic418967fa.accept_19_8_15_7_1_323 27 34 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 34 216 2 13 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 34 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 34 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 216 2 12 17 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 216 (accept_3_5 23 34 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 216 2 11 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 216 (Polychromatic418967fa.accept_23_21_11_9_1_6020
  21 34 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 34 216 2 10 17 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 34 216
  (Polychromatic418967fa.accept_21_19_13_6_1_3550 19 34 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 34 216 2 9 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 34 216 (accept_3_5 17 34 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34
  216 2 8 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  34 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 34 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 34 216 2 7 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 34 216 (Polychromatic418967fa.accept_15_13_4_6_1_3046 13 34 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 216 2 6 17 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 216 (accept_3_5 11 34 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 216 2 5 17 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 216
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 34 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 216 2 4 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 216 (Polychromatic418967fa.accept_21_7_13_6_1_349 7 34 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 216 2 3 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 216 (accept_3_5 5 34 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 216 2 2 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 216 (Polychromatic418967fa.accept_19_3_15_7_1_12710 3 34 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 216 2 1 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 216 (Polychromatic418967fa.accept_25_1_9_16_1_12709
  1 34 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34
  216)))))))))))))))))))))))))))))))))) (allB_succ 33 216 (allA_succ_of_accept 32 33 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 33 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 216 (Polychromatic418967fa.accept_15_1_3_6_1_621 31 33 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 216 3 10 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 29
  33 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 216
  (Polychromatic418967fa.accept_10_8_3_6_1_685 28 33 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 33 216 3 9 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 33 216 (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 33 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 33 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 216 3 8 11 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 216
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 23 33 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 33 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 216 3 7 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 216 (Polychromatic418967fa.accept_15_5_3_6_1_2128 20 33 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 216
  (Polychromatic418967fa.accept_10_9_3_6_1_686 19 33 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 33 216 3 6 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 33 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 17 33 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 216 (Polychromatic418967fa.accept_13_3_7_8_1_4192 16 33 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 216 3 5 11 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 216
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 14 33 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 216 (Polychromatic418967fa.accept_14_13_5_6_1_2747 13 33 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 216 3 4 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 33 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 216
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 10 33 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 33 216 3 3 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 33 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 33 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 33 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 216 3 2 11 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 216
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 33 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 33 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 216 3 1 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 216 (Polychromatic418967fa.accept_13_2_7_8_1_4221 2 33 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 33 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 216))))))))))))))))))))))))))))))))) (allB_succ 32 216 (allA_succ_of_accept 31 32 216 (accept_3_4 31 32
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 216 2 15 16 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 216
  (Polychromatic418967fa.accept_31_29_1_30_1_12708 29 32 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 216 4 7 8 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 216 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 32 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 216 2 13 16 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 216 (accept_3_4 25 32 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 216 8 3 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 32 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 216 2 11 16 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 32 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 216 4 5 8 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 216 (accept_3_4 19 32 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  216 2 9 16 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 32 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 216 8 2 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 216 (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 32 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 216 2 7 16 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 216 (accept_3_4 13 32 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 216 4 3 8 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 32 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 32 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 216 2 5 16 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 32 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 216 8 1 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 216 (accept_3_4 7 32 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 216
  2 3 16 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  216 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 32 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 216 4 1 8 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 32 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 216 2 1 16 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 216 (accept_3_4 1 32 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 216)))))))))))))))))))))))))))))))) (allB_succ 31 216 (allA_succ_of_accept 30 31 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 216 (accept_3_5 29 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 216 (Polychromatic418967fa.accept_16_12_15_8_1_4586 28 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 31 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 216 (accept_3_5 26 31 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 31 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 216
  (Polychromatic418967fa.accept_11_2_9_7_1_124 24 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 216 (accept_3_5 23 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 216 (Polychromatic418967fa.accept_20_1_11_16_1_699 21 31 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 216 (accept_3_5 20 31 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 216 (Polychromatic418967fa.accept_22_19_9_18_1_12707 19 31
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 216 (accept_3_5 17 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 31 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 216 (accept_3_5 14 31 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 216 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 31 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 216
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 216 (accept_3_5 11 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 216 (Polychromatic418967fa.accept_13_10_5_8_1_2555 10 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 31 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 216 (accept_3_5 8 31 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 31 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 216
  (Polychromatic418967fa.accept_20_6_11_16_1_3992 6 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 216 (accept_3_5 5 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  216 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 31 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 216 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 31 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 216 (accept_3_5 2 31 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 1 31 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 216))))))))))))))))))))))))))))))) (allB_succ 30 216
  (allA_succ_of_accept 29 30 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 30 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 216 2 14 15 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 216 3 9 10 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 216 2 13 15 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 30 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 30 216 6 4 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 216 (Polychromatic418967fa.accept_13_10_4_8_1_2570 23 30 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 216 2 11 15 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 30 216 3 7 10 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 216 2 10 15 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 216
  (Polychromatic418967fa.accept_20_19_10_16_1_7001 19 30 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 30 216 6 3 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 30 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 30 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 216 2 8 15 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 216 3 5 10 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 216 2 7 15 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 216
  (Polychromatic418967fa.accept_19_13_11_7_1_4451 13 30 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 216 6 2 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 30 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 216 2 5 15 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 216 3 3 10 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 30 216 2 4 15 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 216 (Polychromatic418967fa.accept_21_7_9_6_1_8212 7
  30 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 216 6 1 5 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 216
  (Polychromatic418967fa.accept_20_5_10_16_1_9890 5 30 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 216 2 2 15 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 30 216 3 1 10 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 30 216 2 1 15 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 30 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 216)))))))))))))))))))))))))))))) (allB_succ 29 216 (allA_succ_of_accept
  28 29 216 (accept_3_4 28 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 216
  (Polychromatic418967fa.accept_16_11_13_8_1_1578 27 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 29 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 216 (accept_3_4 25 29 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 216 (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 29 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 216 (accept_3_4 22 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 216 (Polychromatic418967fa.accept_14_7_1_6_1_3514 21 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 20 29 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 216 (accept_3_4 19 29 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 216 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 29 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 216
  (Polychromatic418967fa.accept_19_17_10_7_1_11430 17 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 29 216 (accept_3_4 16 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 29 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 29 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 216 (Polychromatic418967fa.accept_19_14_10_7_1_8723 14 29
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 216 (accept_3_4 13 29 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 12
  29 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 216
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 11 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 216 (accept_3_4 10 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 216 (Polychromatic418967fa.accept_15_8_14_6_1_3003 8 29 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 216 (accept_3_4 7 29 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 216 (Polychromatic418967fa.accept_22_6_7_18_1_9725 6 29 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 216 (accept_3_4 4 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  216 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 29 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 29 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 216 (accept_3_4 1 29 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 216))))))))))))))))))))))))))))) (allB_succ 28 216 (allA_succ_of_accept 27 28 216
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 28 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 216 2 13 14 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 28 216 (Polychromatic418967fa.accept_16_9_12_8_1_1554 25 28 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 216 4 6 7 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 216 (accept_3_5 23 28 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 216 2 11 14 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 216 (Polychromatic418967fa.accept_16_5_12_8_1_2521 21 28 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 216 4 5 7 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 216
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 28 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 216 2 9 14 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 216 (accept_3_5 17 28 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  216 4 4 7 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 216 (Polychromatic418967fa.accept_16_15_12_8_1_4585 15 28 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 216 2 7 14 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 28 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 28 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 216 4 3 7 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 216 (accept_3_5 11 28 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 216 2 5 14 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 216 (Polychromatic418967fa.accept_16_9_12_8_1_1554 9
  28 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 216 4 2 7 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 216
  (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 28 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 28 216 2 3 14 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 216 (accept_3_5 5 28 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 216
  4 1 7 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 28 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 216 2 1 14 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 28 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 216)))))))))))))))))))))))))))) (allB_succ 27 216 (allA_succ_of_accept 26
  27 216 (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 27 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 216 (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 27 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 216 3 8 9 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 23 27 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 216 (Polychromatic418967fa.accept_13_9_1_8_1_1742 22 27 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 216 3 7 9 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 216 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 27 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 216
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 27 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 27 216 9 2 3 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 27 216 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 27 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 216 (Polychromatic418967fa.accept_19_16_8_7_1_7226 16 27
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 216 3 5 9 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 216
  (Polychromatic418967fa.accept_19_14_8_7_1_12706 14 27 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 27 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 216 3 4 9 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 11 27 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 216
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 10 27 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 27 216 9 1 3 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 27 216 (Polychromatic418967fa.accept_17_8_10_12_1_5335 8 27 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 216 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 27 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 216 3 2 9 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 216
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 5 27 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 216 (Polychromatic418967fa.accept_16_4_11_8_1_1574 4 27 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 216 3 1 9 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 216 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 27 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 1 27 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 216))))))))))))))))))))))))))) (allB_succ 26 216 (allA_succ_of_accept 25 26 216 (accept_3_4 25 26 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 216 2 12 13 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 216
  (Polychromatic418967fa.accept_25_23_1_16_1_11081 23 26 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 216 2 11 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 216 (Polychromatic418967fa.accept_17_4_9_12_1_9167 21 26 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 216 2 10 13 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 216 (accept_3_4 19 26 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 216 2 9 13 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 216
  (Polychromatic418967fa.accept_15_2_11_6_1_2135 17 26 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 26 216 2 8 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 26 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 26 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 216 2 7 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 216 (accept_3_4 13 26 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 216 2 6 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 26 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 216 2 5 13 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 216
  (Polychromatic418967fa.accept_15_9_11_6_1_637 9 26 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 26 216 2 4 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 26 216 (accept_3_4 7 26 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 216
  2 3 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26
  216 (Polychromatic418967fa.accept_15_5_11_6_1_692 5 26 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 26 216 2 2 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 26 216 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 26 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 216 2 1 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 216 (accept_3_4 1 26 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 26 216)))))))))))))))))))))))))) (allB_succ 25 216 (allA_succ_of_accept 24 25 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 25 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 216 (accept_3_5 23 25 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 216 (Polychromatic418967fa.accept_13_9_12_8_1_570 22 25 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 25 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 216 (accept_3_5 20 25 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 25 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 216
  (Polychromatic418967fa.accept_13_5_12_8_1_198 18 25 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 216 (accept_3_5 17 25 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 25 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 216 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 25 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 216 (accept_3_5 14 25 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 216 (Polychromatic418967fa.accept_19_13_6_7_1_8709 13 25 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 216 (accept_3_5 11 25 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 25 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 25 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 216 (accept_3_5 8 25 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 216 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 25 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 216
  (Polychromatic418967fa.accept_22_6_3_18_1_8074 6 25 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 216 (accept_3_5 5 25 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  216 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 25 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 25 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 216 (accept_3_5 2 25 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 25 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 216))))))))))))))))))))))))) (allB_succ 24 216
  (allA_succ_of_accept 23 24 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 216 2 11 12 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 216 3 7 8 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 216 4 5 6 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 216 (Polychromatic418967fa.accept_13_6_11_8_1_1111
  19 24 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 216 6 3 4 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 216
  (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 24 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 216 8 2 3 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 216 3 5 8 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 216 2 7 12 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 216 (Polychromatic418967fa.accept_19_13_5_7_1_12705 13 24 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 216 12 1 2 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 216 2 5 12 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 216 3 3 8 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 216 8 1 3 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 216
  (Polychromatic418967fa.accept_21_7_3_6_1_8322 7 24 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 216 6 1 4 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 24 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 216 4 1 6 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 216 3 1 8 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 216 2 1 12 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 216 (Polychromatic418967fa.accept_13_1_11_8_1_2562 1 24 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 216)))))))))))))))))))))))) (allB_succ 23
  216 (allA_succ_of_accept 22 23 216 (accept_3_4 22 23 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 23 216 (Polychromatic418967fa.accept_19_2_4_7_1_10048 21 23 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 216 (Polychromatic418967fa.accept_13_7_10_8_1_567 20 23 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 216 (accept_3_4 19 23 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 23 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 23 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 216 (accept_3_4 16 23 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 23 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 216 (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 23 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 216 (accept_3_4 13 23 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 216 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 23
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 216 (accept_3_4 10 23 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 23 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 23 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 216 (accept_3_4 7 23 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 216 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 23 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 216
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 5 23 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 216 (accept_3_4 4 23 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  216 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 23 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 216 (Polychromatic418967fa.accept_13_2_10_8_1_1126 2 23 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 216 (accept_3_4 1 23 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 216))))))))))))))))))))))) (allB_succ 22 216 (allA_succ_of_accept 21 22 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 22 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 216 2 10 11 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 22 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 22 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 216 2 9 11 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 216 (accept_3_5 17 22 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22 216 2 8 11 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 22 216 (Polychromatic418967fa.accept_19_15_3_7_1_5875
  15 22 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 216 2 7 11 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 216
  (Polychromatic418967fa.accept_15_13_7_6_1_682 13 22 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 22 216 2 6 11 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 22 216 (accept_3_5 11 22 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22
  216 2 5 11 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  22 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 22 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 22 216 2 4 11 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 22 216 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 22 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 216 2 3 11 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 216 (accept_3_5 5 22 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 216 2 2 11 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 22 216 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 22 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 216 2 1 11 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 22 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 216)))))))))))))))))))))) (allB_succ 21 216 (allA_succ_of_accept 20 21 216
  (Polychromatic418967fa.accept_16_4_5_8_1_2425 20 21 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 216 (Polychromatic418967fa.accept_16_3_5_8_1_4543 19 21 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 216 3 6 7 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 17 21 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 216
  (Polychromatic418967fa.accept_19_16_2_7_1_11445 16 21 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 21 216 3 5 7 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 21 216 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 21 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 216 (Polychromatic418967fa.accept_14_13_7_6_1_3525 13 21
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 216 3 4 7 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 216
  (Polychromatic418967fa.accept_16_11_5_8_1_2427 11 21 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 216 (Polychromatic418967fa.accept_22_10_21_18_1_12704 10 21 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 216 3 3 7 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 216 (Polychromatic418967fa.accept_14_8_7_6_1_1159 8
  21 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 216
  (Polychromatic418967fa.accept_10_7_1_6_1_673 7 21 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 21 216 3 2 7 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 21 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 21 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 216 (Polychromatic418967fa.accept_16_4_5_8_1_2425 4 21 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 216 3 1 7 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 216
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 21 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 216 (Polychromatic418967fa.accept_14_1_7_6_1_3604 1 21 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 21 216))))))))))))))))))))) (allB_succ 20 216 (allA_succ_of_accept 19 20 216
  (accept_3_4 19 20 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 216 2 9 10 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 216
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 17 20 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 216 4 4 5 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 216 (Polychromatic418967fa.accept_13_2_7_8_1_4221 15 20 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 216 2 7 10 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 216 (accept_3_4 13 20 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 216 4 3 5 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 20 216 (Polychromatic418967fa.accept_15_11_5_6_1_669 11 20 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 216 2 5 10 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 216
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 20 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 216 4 2 5 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 216 (accept_3_4 7 20 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 216
  2 3 10 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  216 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 20 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 216 4 1 5 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 216 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 20 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 216 2 1 10 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 216 (accept_3_4 1 20 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 216)))))))))))))))))))) (allB_succ 19 216 (allA_succ_of_accept 18 19 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 19 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 216 (accept_3_5 17 19 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 216 (Polychromatic418967fa.accept_23_16_19_9_1_12703 16 19 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 19 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 216 (accept_3_5 14 19 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 19 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 216
  (Polychromatic418967fa.accept_16_12_3_8_1_5729 12 19 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 216 (accept_3_5 11 19 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 216 (Polychromatic418967fa.accept_15_10_4_6_1_2129 10 19 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 216 (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 19 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 216 (accept_3_5 8 19 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 216 (Polychromatic418967fa.accept_17_7_2_12_1_1069 7 19 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 216
  (Polychromatic418967fa.accept_17_6_2_12_1_1992 6 19 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 216 (accept_3_5 5 19 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  216 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 19 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 19 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 216 (accept_3_5 2 19 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 19 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 216))))))))))))))))))) (allB_succ 18 216 (allA_succ_of_accept 17
  18 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 18 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 18 216 2 8 9 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 18 216 3 5 6 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 18 216 2 7 9 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 18 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 216 6 2 3 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 216 (Polychromatic418967fa.accept_15_11_3_6_1_1306
  11 18 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 216 2 5 9 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 18 216 9 1 2 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 18 216 2 4 9 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 216
  (Polychromatic418967fa.accept_21_7_18_6_1_9797 7 18 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 216 6 1 3 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 18 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 216 2 2 9 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 216 3 1 6 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 216 2 1 9 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 1 18 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 216)))))))))))))))))) (allB_succ 17 216
  (allA_succ_of_accept 16 17 216 (accept_3_4 16 17 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 216 (Polychromatic418967fa.accept_16_15_1_8_1_1585 15 17 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 216 (Polychromatic418967fa.accept_23_14_17_9_1_12702 14 17 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 216 (accept_3_4 13 17 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 17 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 17 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 216 (accept_3_4 10 17 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 17 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 216 (Polychromatic418967fa.accept_15_8_2_6_1_2125 8 17 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 216 (accept_3_4 7 17 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 216 (Polychromatic418967fa.accept_20_6_17_16_1_8470 6 17 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 216 (Polychromatic418967fa.accept_19_5_17_7_1_7252
  5 17 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 216 (accept_3_4 4 17
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 3 17 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 17 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 216 (accept_3_4 1 17 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 216))))))))))))))))) (allB_succ 16 216 (allA_succ_of_accept 15 16 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 16 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 216 2 7 8 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 216 (Polychromatic418967fa.accept_17_13_16_12_1_6562 13 16 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 216 4 3 4 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 216 (accept_3_5 11 16 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 216 2 5 8 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 216 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 16 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 216 8 1 2 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7
  16 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 216 2 3 8 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 216 (accept_3_5 5 16
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 216 4 1 4 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 16 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 216 2 1 8 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 16 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 216)))))))))))))))) (allB_succ 15 216 (allA_succ_of_accept 14 15 216
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 15 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 216 (Polychromatic418967fa.accept_19_13_15_7_1_5843 13 15 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 216 3 4 5 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 15 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 216
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 10 15 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 216 3 3 5 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 216 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 15 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 216 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 15 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 216 3 2 5 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 15 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 15 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 216 3 1 5 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 15 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 1 15 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 216))))))))))))))) (allB_succ 14 216 (allA_succ_of_accept 13 14 216 (accept_3_4 13 14 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 216 2 6 7 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 216 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 14 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 216 2 5 7 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 216
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 14 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 216 2 4 7 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 14 216 (accept_3_4 7 14 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 216
  2 3 7 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14
  216 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 14 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 216 2 2 7 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 216 (Polychromatic418967fa.accept_19_3_14_7_1_7204 3 14 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 216 2 1 7 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 216 (accept_3_4 1 14 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 216)))))))))))))) (allB_succ 13 216 (allA_succ_of_accept 12 13 216
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 13 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 216 (accept_3_5 11 13 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 216 (Polychromatic418967fa.accept_23_10_13_9_1_12701 10 13 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 13 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 216 (accept_3_5 8 13 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 13 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 216
  (Polychromatic418967fa.accept_19_6_13_7_1_4464 6 13 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 216 (accept_3_5 5 13 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  216 (Polychromatic418967fa.accept_15_4_13_6_1_642 4 13 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 216 (Polychromatic418967fa.accept_16_3_13_8_1_1594 3 13 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 216 (accept_3_5 2 13 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 216 (Polychromatic418967fa.accept_17_1_13_12_1_1084 1 13 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 216))))))))))))) (allB_succ 12 216
  (allA_succ_of_accept 11 12 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 216 2 5 6 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 12 216 3 3 4 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 12 216 4 2 3 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 216 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 12 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 216 6 1 2 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 216
  (Polychromatic418967fa.accept_13_5_12_8_1_198 5 12 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 216 4 1 3 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 12 216 3 1 4 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 12 216 2 1 6 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 216)))))))))))) (allB_succ 11 216 (allA_succ_of_accept 10 11 216
  (accept_3_4 10 11 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 11 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 216 (Polychromatic418967fa.accept_19_8_11_7_1_11474 8 11 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 216 (accept_3_4 7 11 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 216 (Polychromatic418967fa.accept_13_6_11_8_1_1111 6 11 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  11 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 216 (accept_3_4 4 11 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  11 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 11 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 216 (accept_3_4 1 11 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  216))))))))))) (allB_succ 10 216 (allA_succ_of_accept 9 10 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 10 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 216 2 4 5 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 216
  (Polychromatic418967fa.accept_13_7_10_8_1_567 7 10 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 216 2 3 5 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 216 (accept_3_5 5 10 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 216
  2 2 5 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10
  216 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 10 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 10 216 2 1 5 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 10 216 (Polychromatic418967fa.accept_15_1_10_6_1_631 1 10 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 216)))))))))) (allB_succ 9 216 (allA_succ_of_accept 8 9 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 9 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 216 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 9 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 216 3 2 3 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 9 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 9 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 216 3 1 3 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 216 (Polychromatic418967fa.accept_11_2_9_7_1_124 2 9 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 9 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 216))))))))) (allB_succ 8 216
  (allA_succ_of_accept 7 8 216 (accept_3_4 7 8 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 216 2
  3 4 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 8 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 216 4 1 2 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 8 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 216 2 1 4 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 216 (accept_3_4 1 8 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 216)))))))) (allB_succ 7 216 (allA_succ_of_accept 6 7 216
  (Polychromatic418967fa.accept_20_6_7_16_1_5437 6 7 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 216 (accept_3_5 5 7 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 216
  (Polychromatic418967fa.accept_16_4_7_8_1_5753 4 7 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 7 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 216 (accept_3_5 2 7 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 7 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 216))))))) (allB_succ 6 216 (allA_succ_of_accept 5 6 216
  (Polychromatic418967fa.accept_19_5_6_7_1_10003 5 6 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 216 2 2 3 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 6 216 3 1 2 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 6 216 2 1 3 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 6 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 216)))))) (allB_succ 5 216 (allA_succ_of_accept 4 5 216 (accept_3_4 4 5
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 216
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 5 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 216 (Polychromatic418967fa.accept_19_2_5_7_1_10021 2 5 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 216 (accept_3_4 1 5 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 216))))) (allB_succ 4 216 (allA_succ_of_accept 3 4 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 4 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 4 216 2 1 2 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 4 216 (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 4 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 4 216)))) (allB_succ 3 216 (allA_succ_of_accept 2 3 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 3 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 216 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 3 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 216))) (allB_succ 2 216 (allA_succ_of_accept 1 2 216 (accept_3_4 1 2 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 216)) (allB_two
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


