-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch222_Segment000
-- name    : Polychromatic418967fa_Branch222_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:33:39.008186+00:00
-- url     : https://prove2.me/theorems/4d62f2e3-aa7c-4a14-958d-6bba50bf093b
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

def Polychromatic418967fa.branch_222_segment_000 : allB 101 222 :=
  allB_succ 100 222 (allA_succ_of_accept 99 100 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 99 100 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 100 222 2 49 50 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 100 222
  (Polychromatic418967fa.accept_9_7_1_6_1_261 97 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 100 222 2 48 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 100 222 (accept_3_5 95 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 100 222 2 47 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 100 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 93 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 100 222 2 46 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 100 222
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 91 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 100 222 2 45 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 100 222 (accept_3_5 89 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 100 222 2 44 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 100 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 87 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 100 222 2 43 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 100 222
  (Polychromatic418967fa.accept_9_4_1_6_1_284 85 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 100 222 2 42 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 100 222 (accept_3_5 83 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 100 222 2 41 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 100 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 100 222 2 40 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 100 222
  (Polychromatic418967fa.accept_9_7_1_6_1_261 79 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 100 222 2 39 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 100 222 (accept_3_5 77 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 100 222 2 38 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 100 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 75 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 100 222 2 37 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 100 222
  (Polychromatic418967fa.accept_7_3_2_5_1_147 73 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 100 222 2 36 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 100 222 (accept_3_5 71 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 100 222 2 35 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 100 222 (Polychromatic418967fa.accept_11_3_1_2_1_1063 69 100 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 100 222 2 34 50 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 100 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 67 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 100 222 2 33 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 100 222 (accept_3_5 65 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 100 222 2 32 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 100 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 100 222 2 31 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 100 222
  (Polychromatic418967fa.accept_9_7_1_6_1_261 61 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 100 222 2 30 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 100 222 (accept_3_5 59 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 100 222 2 29 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 100 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 100 222 2 28 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 100 222
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 55 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 100 222 2 27 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 100 222 (accept_3_5 53 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 100 222 2 26 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 100 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 51 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 222 2 25 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 222
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 222 2 24 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 222 (accept_3_5 47 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 222 2 23 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 100 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 100 222 2 22 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 100 222
  (Polychromatic418967fa.accept_9_7_1_6_1_261 43 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 100 222 2 21 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 100 222 (accept_3_5 41 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 222 2 20 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 100 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 222 2 19 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 222
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 100 222 2 18 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 100 222 (accept_3_5 35 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 100 222 2 17 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 100 222 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 222 2 16 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 222
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 100 222 2 15 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 100 222 (accept_3_5 29 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 100 222 2 14 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 100 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 222 2 13 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 100 222 2 12 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 100 222 (accept_3_5 23 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 100 222 2 11 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 100 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 222 2 10 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 222
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 100 222 2 9 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 100 222 (accept_3_5 17 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 100 222 2 8 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 100 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 100 222 2 7 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 222
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 100 222 2 6 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 100 222 (accept_3_5 11 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 100 222 2 5 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 100 222 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 100 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 222 2 4 50 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 222
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 100 222 2 3 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 100 222 (accept_3_5 5 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100
  222 2 2 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  100 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 100 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 100 222 2 1 50 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 100 222 (Polychromatic418967fa.accept_16_1_4_14_1_1896 1 100 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  222 (allA_succ_of_accept 98 99 222 (Polychromatic418967fa.accept_12_2_3_6_1_112 98 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 99 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 99 222 3 32 33 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 99 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 95 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 99 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 94 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 222 3 31 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 92
  99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 99 222
  (Polychromatic418967fa.accept_10_1_9_2_1_45 91 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 99 222 3 30 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 99 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 88 99 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 99 222 3 29 33 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 99 222
  (Polychromatic418967fa.accept_12_2_3_6_1_112 86 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 222 3 28 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 83
  99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 222
  (Polychromatic418967fa.accept_12_10_3_6_1_882 82 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 99 222 3 27 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 99 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 80 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 222 (Polychromatic418967fa.accept_15_4_9_12_1_2495 79 99
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 99 222 3 26 33 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 99 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 99 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 222 3 25 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 74
  99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 99 222 3 24 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 99 222 (Polychromatic418967fa.accept_10_1_9_2_1_45 71 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 222 (Polychromatic418967fa.accept_12_10_3_6_1_882 70 99 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 99 222 3 23 33 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 99 222
  (Polychromatic418967fa.accept_12_8_3_6_1_909 68 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 222 3 22 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 99
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 222
  (Polychromatic418967fa.accept_12_4_3_6_1_879 64 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 99 222 3 21 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 99 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 62 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 99 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 99 222 3 20 33 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 99 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 59 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 99 222 (Polychromatic418967fa.accept_12_10_3_6_1_882 58 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 222 3 19 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 56
  99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 55 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 99 222 3 18 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 99 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 99 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 99 222 3 17 33 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 99 222
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 222 3 16 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 222 (Polychromatic418967fa.accept_10_7_9_2_1_1887
  47 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 46 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 99 222 3 15 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 99 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 222 (Polychromatic418967fa.accept_16_11_3_14_1_5043 43 99
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 99 222 3 14 33 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 99 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 222 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 222 3 13 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 38
  99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 99 222 3 12 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 99 222 (Polychromatic418967fa.accept_13_9_8_1_1_824 35 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 99 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99 222 3 11 33 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 99 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 222 3 10 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 99
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 222
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 99 222 3 9 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 99 222 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 99 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 99 222 3 8 33 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 99 222
  (Polychromatic418967fa.accept_20_3_19_2_1_5926 23 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 222 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 222 3 7 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 99 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 222
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 19 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 99 222 3 6 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 99 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 222 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 99 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 99 222 3 5 33 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 99 222
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 222 3 4 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 99 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 10 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 99 222 3 3 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 99 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 222 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 99 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 222 3 2 33 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 99 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 222 3 1 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 222 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 99 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 98 222 (allA_succ_of_accept 97 98 222 (accept_3_4 97 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 98 222 2 48 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 98 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 95 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 222 2 47 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 222
  (Polychromatic418967fa.accept_9_3_8_6_1_80 93 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 98 222 2 46 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 98 222 (accept_3_4 91 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 98 222 2 45 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 98 222 (Polychromatic418967fa.accept_11_1_10_2_1_58 89 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 98 222 2 44 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 98 222
  (Polychromatic418967fa.accept_12_3_2_6_1_138 87 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 98 222 2 43 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 98 222 (accept_3_4 85 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 98 222 2 42 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 98 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 83 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 222 2 41 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 222
  (Polychromatic418967fa.accept_12_9_2_6_1_455 81 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 222 2 40 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 98 222 (accept_3_4 79 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 222 2 39 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 98 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 77 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 98 222 2 38 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 98 222
  (Polychromatic418967fa.accept_9_3_8_6_1_80 75 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 98 222 2 37 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 98 222 (accept_3_4 73 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 98 222 2 36 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 98 222 (Polychromatic418967fa.accept_13_6_7_1_1_335 71 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 222 2 35 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 222
  (Polychromatic418967fa.accept_12_9_2_6_1_455 69 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 98 222 2 34 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 98 222 (accept_3_4 67 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 98 222 2 33 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 98 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 65 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 222 2 32 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 222
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 98 222 2 31 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 98 222 (accept_3_4 61 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 98 222 2 30 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 98 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 222 2 29 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 222
  (Polychromatic418967fa.accept_9_3_8_6_1_80 57 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 98 222 2 28 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 98 222 (accept_3_4 55 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 98 222 2 27 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 98 222 (Polychromatic418967fa.accept_17_2_13_1_1_3355 53 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 222 2 26 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 222
  (Polychromatic418967fa.accept_12_3_2_6_1_138 51 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 222 2 25 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 98 222 (accept_3_4 49 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 98 222 2 24 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 98 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 222 2 23 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 222
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 222 2 22 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 98 222 (accept_3_4 43 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 222 2 21 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 98 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 222 2 20 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 222
  (Polychromatic418967fa.accept_9_3_8_6_1_80 39 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 222 2 19 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 98 222 (accept_3_4 37 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 98 222 2 18 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 98 222 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 222 2 17 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 222
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 222 2 16 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 222 (accept_3_4 31 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 222 2 15 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 222 2 14 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 222
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 222 2 13 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 98 222 (accept_3_4 25 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 98 222 2 12 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 98 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 222 2 11 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 222
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 98 222 2 10 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 98 222 (accept_3_4 19 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 222 2 9 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 222 (Polychromatic418967fa.accept_20_17_18_2_1_8937 17 98 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 222 2 8 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 222 (Polychromatic418967fa.accept_10_5_8_2_1_517 15
  98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 222 2 7 49 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 222 (accept_3_4 13
  98 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 222 2 6 49 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 98 222
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 98 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 98 222 2 5 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 98 222 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 98 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 222 2 4 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 222 (accept_3_4 7 98 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 98 222 2 3 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 98 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 98 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 222 2 2 49 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 98
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 222 2 1 49 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 222 (accept_3_4 1 98
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  222 (allA_succ_of_accept 96 97 222 (Polychromatic418967fa.accept_13_5_6_1_1_822 96 97 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 222 (accept_3_5 95 97 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 94 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 93
  97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 222 (accept_3_5 92 97
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62
  91 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 222
  (Polychromatic418967fa.accept_14_6_13_12_1_810 90 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 222 (accept_3_5 89 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 88 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 222 (accept_3_5 86 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 85 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 222
  (Polychromatic418967fa.accept_9_3_7_6_1_76 84 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 222 (accept_3_5 83 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 82 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 222 (accept_3_5 80 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 78 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 222 (accept_3_5 77 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 76 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 222 (accept_3_5 74 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 222
  (Polychromatic418967fa.accept_13_7_6_1_1_368 72 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 222 (accept_3_5 71 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 222 (Polychromatic418967fa.accept_11_4_9_2_1_259 70 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 222 (Polychromatic418967fa.accept_10_9_7_2_1_887 69 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 222 (accept_3_5 68 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 222
  (Polychromatic418967fa.accept_9_3_7_6_1_76 66 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 222 (accept_3_5 65 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 222 (accept_3_5 62 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 222 (Polychromatic418967fa.accept_13_9_6_1_1_2902 61 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 222 (accept_3_5 59 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 222 (accept_3_5 56 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 222
  (Polychromatic418967fa.accept_10_4_7_2_1_211 54 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 222 (accept_3_5 53 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 222 (Polychromatic418967fa.accept_16_4_1_14_1_3908 52 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 222 (accept_3_5 50 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 222
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 222 (accept_3_5 47 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 222 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 222 (accept_3_5 44 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 222
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 222 (accept_3_5 41 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 222 (accept_3_5 38 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 222 (accept_3_5 35 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 222 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 222 (Polychromatic418967fa.accept_13_7_6_1_1_368 33 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 222 (accept_3_5 32 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 222
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 222 (accept_3_5 29 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 222 (accept_3_5 26 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 222
  (Polychromatic418967fa.accept_10_4_7_2_1_211 24 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 222 (accept_3_5 23 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 222 (accept_3_5 20 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 222 (accept_3_5 17 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 222 (Polychromatic418967fa.accept_13_3_6_1_1_3797 16 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 222 (accept_3_5 14 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 222
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 222 (accept_3_5 11 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 222 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 222 (accept_3_5 8 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 222
  (Polychromatic418967fa.accept_14_6_13_12_1_810 6 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 222 (accept_3_5 5 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  222 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 97 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 222 (accept_3_5 2 97 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 97 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 222
  (allA_succ_of_accept 95 96 222 (Polychromatic418967fa.accept_13_4_5_1_1_833 95 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 96 222 2 47 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 96 222 3 31 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 96 222 2 46 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 222
  (Polychromatic418967fa.accept_10_1_6_2_1_867 91 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 96 222 6 15 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 96 222 (Polychromatic418967fa.accept_27_8_15_6_1_13225 89 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 222 2 44 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 96 222 3 29 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 96 222 2 43 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 96 222
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 85 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 222 6 14 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 222 (Polychromatic418967fa.accept_19_7_1_13_1_4861 83 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 222 2 41 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 96 222 3 27 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 96 222 2 40 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 222
  (Polychromatic418967fa.accept_22_13_8_2_1_8451 79 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 222 6 13 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 96 222 (Polychromatic418967fa.accept_13_12_5_1_1_1383 77 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 96 222 2 38 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 96 222 3 25 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 96 222 2 37 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 222
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 73 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 96 222 6 12 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 96 222 (Polychromatic418967fa.accept_10_1_6_2_1_867 71 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 222 2 35 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 96 222 3 23 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 96 222 2 34 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 96 222
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 67 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 222 6 11 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 96 222 (Polychromatic418967fa.accept_15_5_6_12_1_916 65 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 222 2 32 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 96 222 3 21 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 96 222 2 31 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 222
  (Polychromatic418967fa.accept_10_1_6_2_1_867 61 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 222 6 10 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 222 (Polychromatic418967fa.accept_17_8_11_1_1_5761 59 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 222 2 29 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 96 222 3 19 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 96 222 2 28 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 222
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 55 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 96 222 6 9 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 96 222 (Polychromatic418967fa.accept_26_1_18_14_1_13224 53 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 222 2 26 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 96 222 3 17 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 96 222 2 25 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 222
  (Polychromatic418967fa.accept_11_5_8_2_1_588 49 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 222 6 8 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 222 (Polychromatic418967fa.accept_13_8_5_1_1_1381 47 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 222 2 23 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 96 222 3 15 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 96 222 2 22 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 222
  (Polychromatic418967fa.accept_13_4_5_1_1_833 43 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 222 6 7 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 222 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 222 2 20 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 96 222 3 13 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 96 222 2 19 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 222
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 37 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 222 6 6 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 96 222 (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 222 2 17 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 96 222 3 11 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 96 222 2 16 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 222
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 222 6 5 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 96 222 (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 222 2 14 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 96 222 3 9 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 96 222 2 13 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 222
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 222 6 4 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 222 (Polychromatic418967fa.accept_27_23_15_6_1_5308 23 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 222 2 11 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 96 222 3 7 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 96 222 2 10 48 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 222
  (Polychromatic418967fa.accept_13_6_5_1_1_834 19 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 222 6 3 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 222 (Polychromatic418967fa.accept_13_4_5_1_1_833 17 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 222 2 8 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 96 222 3 5 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 96 222 2 7 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 222 (Polychromatic418967fa.accept_22_13_8_2_1_8451
  13 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 222 6 2 16 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 222
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 96 222 2 5 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 96 222 3 3 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 96 222 2 4 48 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 222 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 96 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 222 6 1 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 222 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 96 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 222 2 2 48 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 96 222 3 1 32 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 96 222 2 1 48 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 222
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 96 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 95 222 (allA_succ_of_accept 94 95 222 (accept_3_4 94 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 95 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 95 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 95 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 92 95 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 222 (accept_3_4 91 95 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 90
  95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 222 (accept_3_4 88 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 222 (Polychromatic418967fa.accept_10_7_5_2_1_880 87 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 86 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 222 (accept_3_4 85 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 222
  (Polychromatic418967fa.accept_7_6_4_5_1_314 83 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 222 (accept_3_4 82 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 80 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 222 (accept_3_4 79 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 222 (accept_3_4 76 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 74 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 222 (accept_3_4 73 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 222 (accept_3_4 70 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 222 (Polychromatic418967fa.accept_10_8_5_2_1_881 68 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 222 (accept_3_4 67 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 222 (accept_3_4 64 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 222 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 62 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 222 (accept_3_4 61 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 222 (Polychromatic418967fa.accept_17_9_10_1_1_3345 60 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 222
  (Polychromatic418967fa.accept_22_15_7_2_1_11694 59 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 222 (accept_3_4 58 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 56 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 222 (accept_3_4 55 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 222 (Polychromatic418967fa.accept_15_9_5_12_1_1640 54 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 222 (accept_3_4 52 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 222 (accept_3_4 49 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 222
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 222 (accept_3_4 46 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 222 (accept_3_4 43 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 222 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 222 (accept_3_4 40 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 222 (accept_3_4 37 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 222
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 222 (accept_3_4 34 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 222 (Polychromatic418967fa.accept_15_2_5_12_1_369 32 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 222 (accept_3_4 31 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 222 (accept_3_4 28 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 222 (accept_3_4 25 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 222 (Polychromatic418967fa.accept_15_9_5_12_1_1640 24 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 222 (accept_3_4 22 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 222 (accept_3_4 19 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 222 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 222 (accept_3_4 16 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 222 (Polychromatic418967fa.accept_17_14_10_1_1_4523 14 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 222 (accept_3_4 13 95 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 95 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 222
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 222 (accept_3_4 10 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 95 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 95 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 222 (accept_3_4 7 95 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 95 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 95 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 222 (accept_3_4 4 95 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 222 (accept_3_4 1 95 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 222
  (allA_succ_of_accept 93 94 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 93 94 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 94 222 2 46 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 94 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 91 94
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 94 222 2 45 47 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 94 222 (accept_3_5 89
  94 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 94 222 2 44 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 94 222
  (Polychromatic418967fa.accept_10_7_4_2_1_903 87 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 94 222 2 43 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 94 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 85 94 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 94 222 2 42 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 94 222 (accept_3_5 83 94 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 94 222 2 41 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 94 222 (Polychromatic418967fa.accept_11_4_6_2_1_51 81
  94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 94 222 2 40 47 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 94 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 79 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 94 222 2 39 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 94 222 (accept_3_5 77 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 94 222 2 38 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 94 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 75 94 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 94 222 2 37 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 94 222
  (Polychromatic418967fa.accept_9_1_4_6_1_5 73 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 94 222 2 36 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 94 222 (accept_3_5 71 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 94 222 2 35 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 94 222 (Polychromatic418967fa.accept_12_9_10_6_1_872 69 94 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 94 222 2 34 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 94 222
  (Polychromatic418967fa.accept_10_7_4_2_1_903 67 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 94 222 2 33 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 94 222 (accept_3_5 65 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 94 222 2 32 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 94 222 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 94 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 94 222 2 31 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 94 222
  (Polychromatic418967fa.accept_9_7_4_6_1_273 61 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 94 222 2 30 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 94 222 (accept_3_5 59 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 94 222 2 29 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 94 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 94 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 94 222 2 28 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 94 222
  (Polychromatic418967fa.accept_9_1_4_6_1_5 55 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 94 222 2 27 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 94 222 (accept_3_5 53 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 94 222 2 26 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 94 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 94 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 222 2 25 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 222
  (Polychromatic418967fa.accept_17_15_9_1_1_3363 49 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 222 2 24 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 94 222 (accept_3_5 47 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 94 222 2 23 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 94 222 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 94 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 222 2 22 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 222
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 222 2 21 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 94 222 (accept_3_5 41 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 94 222 2 20 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 94 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 94 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 94 222 2 19 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 222 2 18 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 94 222 (accept_3_5 35 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 94 222 2 17 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 94 222 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 94 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 222 2 16 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 222
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 31 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 222 2 15 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 94 222 (accept_3_5 29 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 94 222 2 14 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 94 222 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 94 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 222 2 13 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 222
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 222 2 12 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 94 222 (accept_3_5 23 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 94 222 2 11 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 94 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 94 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 222 2 10 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 222
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 222 2 9 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 222 (accept_3_5 17 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  222 2 8 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 222 2 7 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 94 222 (Polychromatic418967fa.accept_23_13_2_15_1_13223 13 94 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 222 2 6 47 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 222 (accept_3_5 11 94 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 222 2 5 47 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 94 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 222 2 4 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 94 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 222 2 3 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 222 (accept_3_5 5 94 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 222 2 2 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 94 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 222 2 1 47 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 94
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 222
  (allA_succ_of_accept 92 93 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 92 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 222 3 30 31 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 89 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 222 3 29 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 86
  93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 85 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 222 3 28 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 82 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 222 3 27 31 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 222
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 222 3 26 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 77
  93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 76 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 222 3 25 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 74 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 222 3 24 31 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 222 3 23 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 222 3 22 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 222 3 21 31 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 62 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 222 3 20 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 222 3 19 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 222 3 18 31 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 222 3 17 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 222 3 16 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 222 3 15 31 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 222 3 14 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 93 222 3 13 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 222 3 12 31 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 222 3 11 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 32
  93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 93 222 3 10 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 93 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 222 3 9 31 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 222 3 8 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 222 3 7 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 222 3 6 31 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 222
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 222 3 5 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 222 3 4 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 222 3 3 31 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 222 3 2 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 93 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 222 3 1 31 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 93 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 93 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 222
  (allA_succ_of_accept 91 92 222 (accept_3_4 91 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  222 2 45 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 89 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 222 2 44 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 92 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 222 2 43 46 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 222 (accept_3_4 85 92 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 222 2 42 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 83 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 222 2 41 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 92 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 222 2 40 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 222 (accept_3_4 79 92 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 222 2 39 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 77
  92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 222 2 38 46 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 222
  (Polychromatic418967fa.accept_9_3_2_6_1_264 75 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 222 2 37 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 92 222 (accept_3_4 73 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 92 222 2 36 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 92 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 71 92 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 222 2 35 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 92 222 2 34 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 92 222 (accept_3_4 67 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 92 222 2 33 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 92 222 (Polychromatic418967fa.accept_15_5_2_12_1_2543 65 92 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 92 222 2 32 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 92 222
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 92 222 2 31 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 92 222 (accept_3_4 61 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 92 222 2 30 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 92 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 92 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 222 2 29 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 222
  (Polychromatic418967fa.accept_9_3_2_6_1_264 57 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 222 2 28 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 92 222 (accept_3_4 55 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 92 222 2 27 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 92 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 92 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 92 222 2 26 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 92 222
  (Polychromatic418967fa.accept_12_3_8_6_1_895 51 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 92 222 2 25 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 92 222 (accept_3_4 49 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 92 222 2 24 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 92 222 (Polychromatic418967fa.accept_20_7_12_2_1_4465 47 92 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 92 222 2 23 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 92 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 92 222 2 22 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 92 222 (accept_3_4 43 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 92 222 2 21 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 92 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 92 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 222 2 20 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 222 2 19 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 92 222 (accept_3_4 37 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 92 222 2 18 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 92 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 92 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 222 2 17 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 222
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 92 222 2 16 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 92 222 (accept_3_4 31 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 92 222 2 15 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 92 222 (Polychromatic418967fa.accept_15_14_2_12_1_2472 29 92 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 92 222 2 14 46 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 92 222 2 13 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 92 222 (accept_3_4 25 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 92 222 2 12 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 92 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 92 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 222 2 11 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 222
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 222 2 10 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 92 222 (accept_3_4 19 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 92 222 2 9 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 92 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 92 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 222 2 8 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 222 (Polychromatic418967fa.accept_12_3_8_6_1_895 15
  92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 222 2 7 46 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 222 (accept_3_4 13
  92 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 222 2 6 46 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 92 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 92 222 2 5 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 92 222 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 92 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 222 2 4 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 222 (accept_3_4 7 92 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 92 222 2 3 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 92 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 92 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 222 2 2 46 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 92
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 222 2 1 46 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 222 (accept_3_4 1 92
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 222
  (allA_succ_of_accept 90 91 222 (Polychromatic418967fa.accept_17_5_6_1_1_5735 90 91 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 222 (accept_3_5 89 91 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 88 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 222 (Polychromatic418967fa.accept_17_2_6_1_1_8357
  87 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 222 (accept_3_5 86
  91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 85 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 84 91 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 222 (accept_3_5 83 91 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 222 (Polychromatic418967fa.accept_19_6_15_13_1_3498 82 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 91 222 (accept_3_5 80 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  91 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 79 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 91 222 (Polychromatic418967fa.accept_11_1_3_2_1_1090 78 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 222 (accept_3_5 77 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 91 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 222
  (Polychromatic418967fa.accept_9_3_1_6_1_86 75 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 91 222 (accept_3_5 74 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  91 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 222 (Polychromatic418967fa.accept_14_2_7_12_1_1485 72 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 222 (accept_3_5 71 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 91 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 222 (accept_3_5 68 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 66 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 222 (accept_3_5 65 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 222 (Polychromatic418967fa.accept_15_4_1_12_1_914 64 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 222
  (Polychromatic418967fa.accept_10_3_1_2_1_521 63 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 222 (accept_3_5 62 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 222 (Polychromatic418967fa.accept_21_18_7_12_1_10175 60 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 222 (accept_3_5 59 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 91 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 222 (accept_3_5 56 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 222 (Polychromatic418967fa.accept_19_17_15_13_1_7794 55 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 222 (Polychromatic418967fa.accept_17_3_6_1_1_8382 54 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 222 (accept_3_5 53 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 222
  (Polychromatic418967fa.accept_14_9_7_12_1_4034 51 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 222 (accept_3_5 50 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 222 (accept_3_5 47 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 222 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 222 (accept_3_5 44 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 222 (Polychromatic418967fa.accept_19_4_15_13_1_13215 42 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 222 (accept_3_5 41 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 91 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 222
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 222 (accept_3_5 38 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 222 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 222 (accept_3_5 35 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 222 (accept_3_5 32 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 222 (accept_3_5 29 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 222 (Polychromatic418967fa.accept_15_13_1_12_1_1638 28 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 222
  (Polychromatic418967fa.accept_18_9_1_6_1_5301 27 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 222 (accept_3_5 26 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 222 (Polychromatic418967fa.accept_21_3_7_12_1_8725 24 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 222 (accept_3_5 23 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 91 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 222 (accept_3_5 20 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 222 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 222 (Polychromatic418967fa.accept_21_18_7_12_1_10175 18 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 222 (accept_3_5 17 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 91 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 222
  (Polychromatic418967fa.accept_21_15_7_12_1_8686 15 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 222 (accept_3_5 14 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 222 (accept_3_5 11 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 222 (Polychromatic418967fa.accept_22_10_3_2_1_13222 10 91 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 222 (accept_3_5 8 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  222 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 91 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 222 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 91 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 222 (accept_3_5 5 91 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 91 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 222 (accept_3_5 2 91 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 222
  (allA_succ_of_accept 89 90 222 (Polychromatic418967fa.accept_13_11_12_1_1_2154 89 90 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 90 222 2 44 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 90 222 3 29 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 90 222 2 43 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 85 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 90 222 6 14 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 90 222 (Polychromatic418967fa.accept_13_5_12_1_1_2123 83 90 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 222 2 41 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 90 222 3 27 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 90 222 2 40 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 222
  (Polychromatic418967fa.accept_16_15_10_14_1_2872 79 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 90 222 6 13 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 90 222 (Polychromatic418967fa.accept_16_13_10_14_1_2871 77 90 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 222 2 38 45 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 90 222 3 25 30 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 90 222 2 37 45 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 222
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 73 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 222 6 12 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 90 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 222 2 35 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 90 222 3 23 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 90 222 2 34 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 67 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 222 6 11 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 90 222 (Polychromatic418967fa.accept_19_8_14_13_1_11837 65 90 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 222 2 32 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 90 222 3 21 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 90 222 2 31 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 222
  (Polychromatic418967fa.accept_16_13_10_14_1_2871 61 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 90 222 6 10 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 90 222 (Polychromatic418967fa.accept_21_17_6_12_1_10174 59 90 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 222 2 29 45 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 90 222 3 19 30 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 90 222 2 28 45 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 222
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 55 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 222 6 9 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 90 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 222 2 26 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 90 222 3 17 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 90 222 2 25 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 222
  (Polychromatic418967fa.accept_21_7_6_12_1_10316 49 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 222 6 8 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 90 222 (Polychromatic418967fa.accept_13_8_12_1_1_4662 47 90 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 222 2 23 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 222 3 15 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 90 222 2 22 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 222 6 7 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 90 222 (Polychromatic418967fa.accept_13_2_12_1_1_343 41 90 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 222 2 20 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 90 222 3 13 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 90 222 2 19 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 222
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 37 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 222 6 6 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 222 (Polychromatic418967fa.accept_19_16_14_13_1_2313 35 90 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 222 2 17 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 90 222 3 11 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 90 222 2 16 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 222
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 31 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 222 6 5 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 90 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 90 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 222 2 14 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 90 222 3 9 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 90 222 2 13 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 222 6 4 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 90 222 (Polychromatic418967fa.accept_16_7_10_14_1_1884 23 90 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 222 2 11 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 90 222 3 7 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 90 222 2 10 45 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 222
  (Polychromatic418967fa.accept_21_19_6_12_1_7089 19 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 222 6 3 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 222 (Polychromatic418967fa.accept_21_17_6_12_1_10174 17 90 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 222 2 8 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 222 3 5 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 222 2 7 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 222 (Polychromatic418967fa.accept_14_13_6_12_1_3126
  13 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 222 6 2 15 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 222 2 5 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 90 222 3 3 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 90 222 2 4 45 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 222 (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 90 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 222 6 1 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 222 (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 90 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 222 2 2 45 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 90 222 3 1 30 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 90 222 2 1 45 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 90 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 222 (allA_succ_of_accept 88 89 222 (accept_3_4 88 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 89 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 86 89 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 222 (accept_3_4 85 89 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 84
  89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 222 (accept_3_4 82 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 222 (Polychromatic418967fa.accept_10_1_9_2_1_45 81 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 222 (Polychromatic418967fa.accept_11_3_1_2_1_1063 80 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 222 (accept_3_4 79 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 222 (Polychromatic418967fa.accept_21_15_5_12_1_3987 78 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 222
  (Polychromatic418967fa.accept_9_5_8_6_1_281 77 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 222 (accept_3_4 76 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 74 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 222 (accept_3_4 73 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 222 (Polychromatic418967fa.accept_13_7_11_1_1_2903 72 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 222 (accept_3_4 70 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 222 (Polychromatic418967fa.accept_11_3_1_2_1_1063 69 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 68 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 222 (accept_3_4 67 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 222
  (Polychromatic418967fa.accept_9_2_8_6_1_79 65 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 222 (accept_3_4 64 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 222 (Polychromatic418967fa.accept_13_10_11_1_1_2152 62 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 222 (accept_3_4 61 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 222 (Polychromatic418967fa.accept_13_8_11_1_1_3789 60 89
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 222 (accept_3_4 58 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 56 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 222 (accept_3_4 55 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 222 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 222
  (Polychromatic418967fa.accept_16_5_9_14_1_5051 53 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 222 (accept_3_4 52 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 50 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 222 (accept_3_4 49 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 222 (accept_3_4 46 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 222 (Polychromatic418967fa.accept_14_3_5_12_1_4000 45 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 222 (Polychromatic418967fa.accept_20_4_9_2_1_213 44 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 222 (accept_3_4 43 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 222 (Polychromatic418967fa.accept_13_3_11_1_1_2122 42 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 222
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 222 (accept_3_4 40 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 222 (accept_3_4 37 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 222 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 222 (accept_3_4 34 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 222 (Polychromatic418967fa.accept_13_7_11_1_1_2903 33 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 222 (accept_3_4 31 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 222
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 222 (accept_3_4 28 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 222 (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 222 (accept_3_4 25 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 222 (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 89
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 222 (accept_3_4 22 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 222 (accept_3_4 19 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 222 (Polychromatic418967fa.accept_21_18_5_12_1_4032 18 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 222
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 222 (accept_3_4 16 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 222 (accept_3_4 13 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 222 (accept_3_4 10 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 222 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 222 (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 222 (accept_3_4 7 89 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 222 (Polychromatic418967fa.accept_21_6_5_12_1_10314 6 89 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 222
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 222 (accept_3_4 4 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 89 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 222 (accept_3_4 1 89 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 222 (allA_succ_of_accept 87 88 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 87 88 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 88 222 2 43 44 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 88 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 85 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 88 222 2 42 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 88 222 (accept_3_5 83 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 88 222 2 41 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 88 222 (Polychromatic418967fa.accept_12_9_4_6_1_460 81 88 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 88 222 2 40 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 88 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 79 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 88 222 2 39 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 88 222 (accept_3_5 77 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 88 222 2 38 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 88 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 75 88 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 88 222 2 37 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 88 222
  (Polychromatic418967fa.accept_9_1_7_6_1_75 73 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 88 222 2 36 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 88 222 (accept_3_5 71 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 88 222 2 35 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 88 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 88 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 88 222 2 34 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 88 222
  (Polychromatic418967fa.accept_9_4_7_6_1_255 67 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 88 222 2 33 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 88 222 (accept_3_5 65 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 88 222 2 32 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 88 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 88 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 88 222 2 31 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 88 222
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 61 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 88 222 2 30 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 88 222 (accept_3_5 59 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 88 222 2 29 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 88 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 88 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 88 222 2 28 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 88 222
  (Polychromatic418967fa.accept_7_6_4_5_1_314 55 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 88 222 2 27 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 88 222 (accept_3_5 53 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 88 222 2 26 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 88 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 88 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 88 222 2 25 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 88 222
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 88 222 2 24 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 88 222 (accept_3_5 47 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 88 222 2 23 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 88 222 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 88 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 88 222 2 22 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 88 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 88 222 2 21 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 88 222 (accept_3_5 41 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 88 222 2 20 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 88 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 88 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 222 2 19 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 222 2 18 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 88 222 (accept_3_5 35 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 88 222 2 17 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 88 222 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 88 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 88 222 2 16 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 88 222
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 88 222 2 15 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 88 222 (accept_3_5 29 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 88 222 2 14 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 88 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 88 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 222 2 13 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 222
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 222 2 12 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 88 222 (accept_3_5 23 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 88 222 2 11 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 88 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 88 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 222 2 10 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 222
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 222 2 9 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 222 (accept_3_5 17 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  222 2 8 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 222 2 7 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 88 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 88 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 222 2 6 44 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 222 (accept_3_5 11 88 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 222 2 5 44 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 88 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 88 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 88 222 2 4 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 88 222 (Polychromatic418967fa.accept_21_7_4_12_1_8684 7 88 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 222 2 3 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 222 (accept_3_5 5 88 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 88 222 2 2 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 88 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 88 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 222 2 1 44 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 88
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 222
  (allA_succ_of_accept 86 87 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 86 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 222 3 28 29 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 222
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 83 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 222 (Polychromatic418967fa.accept_12_10_3_6_1_882 82 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 222 3 27 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 80
  87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 79 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 222 3 26 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 222 (Polychromatic418967fa.accept_12_4_3_6_1_879 76 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 222 3 25 29 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 222
  (Polychromatic418967fa.accept_10_4_7_2_1_211 74 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 222 3 24 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 71
  87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 222
  (Polychromatic418967fa.accept_12_10_3_6_1_882 70 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 222 3 23 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 68 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 222 (Polychromatic418967fa.accept_11_1_10_2_1_58 67 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 222 3 22 29 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 222 3 21 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 222 (Polychromatic418967fa.accept_12_2_3_6_1_112 62
  87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 222 3 20 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 222 (Polychromatic418967fa.accept_10_9_7_2_1_887 59 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 222 3 19 29 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 222
  (Polychromatic418967fa.accept_11_1_10_2_1_58 56 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 222 (Polychromatic418967fa.accept_10_5_7_2_1_516 55 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 222 3 18 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 87
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 222
  (Polychromatic418967fa.accept_12_4_3_6_1_879 52 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 222 3 17 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 222 3 16 29 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 222
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 47 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 222 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 222 3 15 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 44
  87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 222
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 222 3 14 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 222 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 222 3 13 29 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 222
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 222 3 12 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 222 (Polychromatic418967fa.accept_10_5_7_2_1_516 35
  87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 222
  (Polychromatic418967fa.accept_10_4_7_2_1_211 34 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 222 3 11 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 222 (Polychromatic418967fa.accept_13_5_9_1_1_1405 31 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 222 3 10 29 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 222 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 222 3 9 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 222 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 222 3 8 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 222 3 7 29 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 222
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 222 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 222 3 6 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 222 3 5 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 222 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 222 3 4 29 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 222
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 222 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 222 3 3 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 222
  (Polychromatic418967fa.accept_19_7_11_13_1_11853 7 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 222 3 2 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 222 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 87 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 222 3 1 29 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 87 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 222
  (allA_succ_of_accept 85 86 222 (accept_3_4 85 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  222 2 42 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 83 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 222 2 41 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 86 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 222 2 40 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 222 (accept_3_4 79 86 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 222 2 39 43 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 222
  (Polychromatic418967fa.accept_13_12_8_1_1_825 77 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 222 2 38 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 86 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 222 2 37 43 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 222 (accept_3_4 73 86 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 222 2 36 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 71
  86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 222 2 35 43 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 222
  (Polychromatic418967fa.accept_12_9_2_6_1_455 69 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 222 2 34 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 86 222 (accept_3_4 67 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 86 222 2 33 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 86 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 65 86 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 222 2 32 43 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 222
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 222 2 31 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 222 (accept_3_4 61 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 222 2 30 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 86 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 222 2 29 43 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 222
  (Polychromatic418967fa.accept_9_3_5_6_1_253 57 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 222 2 28 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 86 222 (accept_3_4 55 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 222 2 27 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 86 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 222 2 26 43 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 222
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 222 2 25 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 222 (accept_3_4 49 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 222 2 24 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 86 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 222 2 23 43 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 222
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 222 2 22 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 222 (accept_3_4 43 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 222 2 21 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 222 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 86 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 222 2 20 43 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 222 2 19 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 86 222 (accept_3_4 37 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 222 2 18 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 86 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 222 2 17 43 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 222
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 222 2 16 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 86 222 (accept_3_4 31 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 222 2 15 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 86 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 222 2 14 43 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 222
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 222 2 13 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 86 222 (accept_3_4 25 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 222 2 12 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 222 (Polychromatic418967fa.accept_15_8_11_12_1_1626 23 86 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 222 2 11 43 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 222
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 222 2 10 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 86 222 (accept_3_4 19 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 222 2 9 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 86 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 222 2 8 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 222 (Polychromatic418967fa.accept_11_4_9_2_1_259 15
  86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 222 2 7 43 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 222 (accept_3_4 13
  86 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 222 2 6 43 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 86 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 222 2 5 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 222 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 86 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 222 2 4 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 222 (accept_3_4 7 86 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 222 2 3 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 222 (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 86 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 222 2 2 43 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 86
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 222 2 1 43 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 222 (accept_3_4 1 86
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 222
  (allA_succ_of_accept 84 85 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 84 85 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 222 (accept_3_5 83 85 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 82 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 81
  85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 222 (accept_3_5 80 85
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62
  79 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 222
  (Polychromatic418967fa.accept_10_8_5_2_1_881 78 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 222 (accept_3_5 77 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 222 (accept_3_5 74 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 85 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 222
  (Polychromatic418967fa.accept_19_15_9_13_1_4838 72 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 222 (accept_3_5 71 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 222 (accept_3_5 68 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 85 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 222 (accept_3_5 65 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 222 (accept_3_5 62 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 85 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 222 (accept_3_5 59 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 222 (Polychromatic418967fa.accept_10_8_5_2_1_881 58 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 222 (accept_3_5 56 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 85 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 222
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 54 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 222 (accept_3_5 53 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 222 (accept_3_5 50 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 222 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 85 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 222 (accept_3_5 47 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 222 (accept_3_5 44 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 85 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 222
  (Polychromatic418967fa.accept_13_3_7_1_1_334 42 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 222 (accept_3_5 41 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 222 (Polychromatic418967fa.accept_21_19_1_12_1_5485 40 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 222 (accept_3_5 38 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 85 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 222
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 222 (accept_3_5 35 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 222 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 222 (accept_3_5 32 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 85 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 222
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 222 (accept_3_5 29 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 222 (accept_3_5 26 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 85 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 222 (accept_3_5 23 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 222 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 222 (accept_3_5 20 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 222 (accept_3_5 17 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 222 (accept_3_5 14 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 85 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 222
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 222 (accept_3_5 11 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 222 (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 222 (accept_3_5 8 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 222 (accept_3_5 5 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  222 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 85 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 222 (accept_3_5 2 85 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 222
  (allA_succ_of_accept 83 84 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84 222 2 41 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 84 222 3 27 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 84 222 2 40 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 222
  (Polychromatic418967fa.accept_9_7_3_6_1_270 79 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 84 222 6 13 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 84 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 77 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 222 2 38 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 84 222 3 25 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 84 222 2 37 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 84 222
  (Polychromatic418967fa.accept_9_1_3_6_1_70 73 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 222 6 12 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 222 (Polychromatic418967fa.accept_9_8_3_6_1_533 71 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 222 2 35 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 84 222 3 23 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 84 222 2 34 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 222 6 11 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84 222 2 32 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 84 222 3 21 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 84 222 2 31 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 222
  (Polychromatic418967fa.accept_9_7_3_6_1_270 61 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 84 222 6 10 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 84 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 59 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 222 2 29 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 84 222 3 19 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 84 222 2 28 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 222
  (Polychromatic418967fa.accept_9_1_3_6_1_70 55 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 222 6 9 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 84 222 (Polychromatic418967fa.accept_9_8_3_6_1_533 53 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 222 2 26 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 84 222 3 17 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 84 222 2 25 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 222 6 8 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 222 2 23 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 84 222 3 15 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 84 222 2 22 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 222
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 222 6 7 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 84 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 222 2 20 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 84 222 3 13 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 84 222 2 19 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 222
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 222 6 6 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 222 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 222 2 17 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 84 222 3 11 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 84 222 2 16 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 222 6 5 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 222 2 14 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 84 222 3 9 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 84 222 2 13 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 222
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 222 6 4 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 222 2 11 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84 222 3 7 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84 222 2 10 42 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 222
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 222 6 3 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 222 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 222 2 8 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 84 222 3 5 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 222 2 7 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 13
  84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 222 6 2 14 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 222
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 84 222 2 5 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 84 222 3 3 28 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 84 222 2 4 42 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 84 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 222 6 1 14 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 84 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 222 2 2 42 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 84 222 3 1 28 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 84 222 2 1 42 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 222
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 84 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 222
  (allA_succ_of_accept 82 83 222 (accept_3_4 82 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 80 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 222 (accept_3_4 79 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 222 (accept_3_4 76 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 74 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 222 (accept_3_4 73 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 222 (Polychromatic418967fa.accept_19_15_7_13_1_11844 72 83 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 71 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 222 (accept_3_4 70 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 68 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 222 (accept_3_4 67 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 222 (accept_3_4 64 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 222 (Polychromatic418967fa.accept_15_3_8_12_1_900 63 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 62 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 222 (accept_3_4 61 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 222
  (Polychromatic418967fa.accept_9_5_2_6_1_265 59 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 222 (accept_3_4 58 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 222 (Polychromatic418967fa.accept_13_4_5_1_1_833 56 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 222 (accept_3_4 55 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 222 (Polychromatic418967fa.accept_17_3_15_1_1_3348 54 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 222 (accept_3_4 52 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 222 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 50 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 222 (accept_3_4 49 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 222
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 47 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 222 (accept_3_4 46 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 222 (accept_3_4 43 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 222 (Polychromatic418967fa.accept_13_3_5_1_1_2144 42 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 222 (accept_3_4 40 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 222 (Polychromatic418967fa.accept_13_12_5_1_1_1383 38 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 222 (accept_3_4 37 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 83 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 222
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 222 (accept_3_4 34 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 222 (accept_3_4 31 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 222 (accept_3_4 28 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 222 (Polychromatic418967fa.accept_16_11_3_14_1_5043 27 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 222 (accept_3_4 25 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 222 (Polychromatic418967fa.accept_19_5_7_13_1_4919 24 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 222
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 222 (accept_3_4 22 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 222 (Polychromatic418967fa.accept_14_6_13_12_1_810 20 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 222 (accept_3_4 19 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 83 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 222 (accept_3_4 16 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 222 (accept_3_4 13 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 83 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 222 (accept_3_4 10 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 83 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 222 (accept_3_4 7 83 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 222 (Polychromatic418967fa.accept_13_6_5_1_1_834 6 83 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 222 (accept_3_4 4 83 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 222
  (Polychromatic418967fa.accept_19_2_7_13_1_2337 2 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 222 (accept_3_4 1 83 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 222
  (allA_succ_of_accept 81 82 222 (Polychromatic418967fa.accept_12_9_10_6_1_872 81 82 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 82 222 2 40 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 82 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 79
  82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 222 2 39 41 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 222 (accept_3_5 77
  82 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 222 2 38 41 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 222
  (Polychromatic418967fa.accept_9_3_1_6_1_86 75 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 82 222 2 37 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 82 222 (Polychromatic418967fa.accept_21_10_19_12_1_10247 73 82 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 82 222 2 36 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 82 222 (accept_3_5 71 82 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 82 222 2 35 41 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 82 222
  (Polychromatic418967fa.accept_12_9_10_6_1_872 69 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 82 222 2 34 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 82 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 82 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 82 222 2 33 41 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 82 222 (accept_3_5 65 82 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 82 222 2 32 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 82 222 (Polychromatic418967fa.accept_11_8_5_2_1_1629
  63 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 82 222 2 31 41 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 82 222
  (Polychromatic418967fa.accept_9_7_1_6_1_261 61 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 82 222 2 30 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 82 222 (accept_3_5 59 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 82 222 2 29 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 82 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 82 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 222 2 28 41 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 222
  (Polychromatic418967fa.accept_13_3_4_1_1_363 55 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 222 2 27 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 82 222 (accept_3_5 53 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 82 222 2 26 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 82 222 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 82 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 82 222 2 25 41 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 82 222
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 82 222 2 24 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 82 222 (accept_3_5 47 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 82 222 2 23 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 82 222 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 82 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 222 2 22 41 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 222
  (Polychromatic418967fa.accept_9_7_1_6_1_261 43 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 82 222 2 21 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 82 222 (accept_3_5 41 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 82 222 2 20 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 82 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 82 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 222 2 19 41 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 222
  (Polychromatic418967fa.accept_27_10_1_6_1_13221 37 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 222 2 18 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 82 222 (accept_3_5 35 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 82 222 2 17 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 82 222 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 82 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 222 2 16 41 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 222
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 222 2 15 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 82 222 (accept_3_5 29 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 82 222 2 14 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 82 222 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 82 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 222 2 13 41 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 222
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 222 2 12 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 82 222 (accept_3_5 23 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 82 222 2 11 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 82 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 82 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 222 2 10 41 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 222
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 222 2 9 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 222 (accept_3_5 17 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  222 2 8 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 222 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 222 2 7 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 82 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 82 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 222 2 6 41 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 222 (accept_3_5 11 82 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 222 2 5 41 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 222
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 222 2 4 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 82 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 222 2 3 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 222 (accept_3_5 5 82 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 222 2 2 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 82 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 222 2 1 41 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 222 (Polychromatic418967fa.accept_21_1_19_12_1_5562
  1 82 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 222
  (allA_succ_of_accept 80 81 222 (Polychromatic418967fa.accept_12_8_9_6_1_127 80 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 81 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 222 3 26 27 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 222
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 77 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 222 3 25 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 222 (Polychromatic418967fa.accept_12_2_9_6_1_439 74
  81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 222
  (Polychromatic418967fa.accept_10_3_1_2_1_521 73 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 222 3 24 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 222 (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 81
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 222 3 23 27 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 222
  (Polychromatic418967fa.accept_12_8_9_6_1_127 68 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 222 3 22 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 65
  81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 64 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 222 3 21 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 62 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 222 (Polychromatic418967fa.accept_11_6_4_2_1_599 61 81 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 222 3 20 27 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 222 3 19 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 222 (Polychromatic418967fa.accept_10_6_1_2_1_874 56
  81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 222 3 18 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 222 (Polychromatic418967fa.accept_10_3_1_2_1_521 53 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 222 (Polychromatic418967fa.accept_12_4_9_6_1_440 52 81 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 222 3 17 27 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 222 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 222 3 16 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 222
  (Polychromatic418967fa.accept_10_6_1_2_1_874 46 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 222 3 15 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 222 3 14 27 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 222
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 222 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 222 3 13 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 222 (Polychromatic418967fa.accept_12_2_9_6_1_439 38
  81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 222 3 12 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 81 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 222 3 11 27 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 222
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 222 3 10 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 29
  81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 222
  (Polychromatic418967fa.accept_11_6_4_2_1_599 28 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 222 3 9 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 222 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 222 (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 81
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 222 3 8 27 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 222 3 7 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 81 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 222 3 6 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 222 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 81 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 222 3 5 27 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 222
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 222 3 4 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 222
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 222 3 3 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 222 3 2 27 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 222
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 222 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 81 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 222 3 1 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 81 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 81 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 222
  (allA_succ_of_accept 79 80 222 (accept_3_4 79 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  222 2 39 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  77 80 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 77 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 222 2 38 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 80 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 80 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 80 222 2 37 40 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 222 (accept_3_4 73 80 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 222 2 36 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 222
  (Polychromatic418967fa.accept_7_1_3_5_1_33 71 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 222 2 35 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 80 222 (Polychromatic418967fa.accept_12_9_8_6_1_466 69 80 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 222 2 34 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 222 (accept_3_4 67 80 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 222 2 33 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 65
  80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 80 222 2 32 40 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 80 222
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 80 222 2 31 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 80 222 (accept_3_4 61 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 80 222 2 30 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 80 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 80 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 222 2 29 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 222
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 222 2 28 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 80 222 (accept_3_4 55 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 80 222 2 27 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 80 222 (Polychromatic418967fa.accept_15_8_5_12_1_4453 53 80 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 80 222 2 26 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 80 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 80 222 2 25 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 80 222 (accept_3_4 49 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 80 222 2 24 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 80 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 80 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 222 2 23 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 222
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 222 2 22 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 80 222 (accept_3_4 43 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 80 222 2 21 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 80 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 80 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 222 2 20 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 222
  (Polychromatic418967fa.accept_9_3_8_6_1_80 39 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 80 222 2 19 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 80 222 (accept_3_4 37 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 80 222 2 18 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 80 222 (Polychromatic418967fa.accept_13_9_2_1_1_813 35 80 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 222 2 17 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 222
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 222 2 16 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 80 222 (accept_3_4 31 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 80 222 2 15 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 80 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 80 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 80 222 2 14 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 80 222
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 80 222 2 13 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 80 222 (accept_3_4 25 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 80 222 2 12 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 80 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 80 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 222 2 11 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 222
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 222 2 10 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 80 222 (accept_3_4 19 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 80 222 2 9 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 80 222 (Polychromatic418967fa.accept_15_2_5_12_1_369 17 80 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 222 2 8 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 222 2 7 40 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 222 (accept_3_4 13
  80 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 222 2 6 40 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 222
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 80 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 80 222 2 5 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 80 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 222 2 4 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 222 (accept_3_4 7 80 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 80 222 2 3 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 80 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 80 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 222 2 2 40 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 80
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 222 2 1 40 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 222 (accept_3_4 1 80
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 222
  (allA_succ_of_accept 78 79 222 (Polychromatic418967fa.accept_17_10_11_1_1_5784 78 79 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 222 (accept_3_5 77 79 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 76 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 75
  79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 222 (accept_3_5 74 79
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3
  73 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 222
  (Polychromatic418967fa.accept_20_12_19_2_1_4421 72 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 222 (accept_3_5 71 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 222 (Polychromatic418967fa.accept_21_7_16_12_1_13220 70 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 222 (accept_3_5 68 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 79 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 222
  (Polychromatic418967fa.accept_7_3_2_5_1_147 66 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 222 (accept_3_5 65 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 64 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 222 (Polychromatic418967fa.accept_14_7_9_12_1_3975 63 79 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 222 (accept_3_5 62 79 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 79 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 222 (accept_3_5 59 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 222 (accept_3_5 56 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 79 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 222
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 54 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 222 (accept_3_5 53 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 222 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 222 (accept_3_5 50 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 79 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 222
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 222 (accept_3_5 47 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 222 (accept_3_5 44 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 222 (Polychromatic418967fa.accept_20_3_19_2_1_5926 43 79 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 222
  (Polychromatic418967fa.accept_16_10_15_14_1_1086 42 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 79 222 (accept_3_5 41 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 79 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 79 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 79 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 222 (accept_3_5 38 79 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 222
  (Polychromatic418967fa.accept_16_4_15_14_1_5056 36 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 222 (accept_3_5 35 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 222 (Polychromatic418967fa.accept_25_9_4_22_1_13219 34 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 222 (accept_3_5 32 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 79 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 222
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 222 (accept_3_5 29 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 222 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 222 (accept_3_5 26 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 222
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 222 (accept_3_5 23 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 222 (accept_3_5 20 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 79 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 222 (accept_3_5 17 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 222 (Polychromatic418967fa.accept_15_1_4_12_1_2401 16 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 222 (Polychromatic418967fa.accept_22_15_13_2_1_13218 15 79 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 222 (accept_3_5 14 79 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 222
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 222 (accept_3_5 11 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 222 (accept_3_5 8 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 222 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 79 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 222
  (Polychromatic418967fa.accept_21_6_16_12_1_1490 6 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 222 (accept_3_5 5 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  222 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 79 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 79 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 222 (accept_3_5 2 79 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 222
  (allA_succ_of_accept 77 78 222 (Polychromatic418967fa.accept_15_2_3_12_1_891 77 78 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 222 2 38 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 78 222 3 25 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 78 222 2 37 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 73 78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 78 222 6 12 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 78 222 (Polychromatic418967fa.accept_21_8_15_12_1_5474 71 78 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 222 2 35 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 78 222 3 23 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 78 222 2 34 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 67 78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 78 222 6 11 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 78 222 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 78 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 222 2 32 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 78 222 3 21 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 78 222 2 31 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 222
  (Polychromatic418967fa.accept_21_19_15_12_1_5523 61 78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 78 222 6 10 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 78 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 78 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 222 2 29 39 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 78 222 3 19 26 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 78 222 2 28 39 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 55 78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 222 6 9 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 78 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 78 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 222 2 26 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 78 222 3 17 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 78 222 2 25 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 222
  (Polychromatic418967fa.accept_19_11_2_13_1_4907 49 78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 222 6 8 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 78 222 (Polychromatic418967fa.accept_11_3_1_2_1_1063 47 78 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 222 2 23 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 78 222 3 15 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 78 222 2 22 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 222
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 222 6 7 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 78 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 222 2 20 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 222 3 13 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 222 2 19 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 222
  (Polychromatic418967fa.accept_15_7_3_12_1_365 37 78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 222 6 6 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 78 222 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 78 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 222 2 17 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 78 222 3 11 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 78 222 2 16 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 222 6 5 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 222 (Polychromatic418967fa.accept_19_10_2_13_1_9183 29 78 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 222 2 14 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 78 222 3 9 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 78 222 2 13 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 222 6 4 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 222 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 78 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 222 2 11 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 78 222 3 7 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 78 222 2 10 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 222
  (Polychromatic418967fa.accept_21_19_15_12_1_5523 19 78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 78 222 6 3 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 78 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 78 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 222 2 8 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 78 222 3 5 26 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 78 222 2 7 39 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 222 6 2 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 78 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 222 2 5 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 78 222 3 3 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 78 222 2 4 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 222 (Polychromatic418967fa.accept_15_7_3_12_1_365 7
  78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 222 6 1 13 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 222
  (Polychromatic418967fa.accept_10_5_8_2_1_517 5 78 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 78 222 2 2 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 78 222 3 1 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 78 222 2 1 39 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 222 (Polychromatic418967fa.accept_19_1_2_13_1_4934 1 78 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 222
  (allA_succ_of_accept 76 77 222 (accept_3_4 76 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 74 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 222 (accept_3_4 73 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 222 (Polychromatic418967fa.accept_14_2_7_12_1_1485 72 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 222 (accept_3_4 70 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 222 (Polychromatic418967fa.accept_10_9_7_2_1_887 69 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 222 (Polychromatic418967fa.accept_21_5_14_12_1_8720 68 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 222 (accept_3_4 67 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 77 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 222
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 222 (accept_3_4 64 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 62 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 222 (accept_3_4 61 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 222 (Polychromatic418967fa.accept_13_8_12_1_1_4662 60 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 222 (accept_3_4 58 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 56 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 222 (accept_3_4 55 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 222 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 222
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 222 (accept_3_4 52 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 222 (Polychromatic418967fa.accept_13_11_12_1_1_2154 50 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 222 (accept_3_4 49 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 77 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 222 (accept_3_4 46 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 222 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 44 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 222 (accept_3_4 43 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 222 (Polychromatic418967fa.accept_16_10_13_14_1_5042 42 77 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 222
  (Polychromatic418967fa.accept_13_2_12_1_1_343 41 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 222 (accept_3_4 40 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 222 (accept_3_4 37 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 222 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 222 (accept_3_4 34 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 222 (Polychromatic418967fa.accept_14_5_7_12_1_4006 33 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 222 (Polychromatic418967fa.accept_17_15_9_1_1_3363 32 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 222 (accept_3_4 31 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 77 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 222
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 222 (accept_3_4 28 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 222 (accept_3_4 25 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 222 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 222 (accept_3_4 22 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 222 (accept_3_4 19 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 222 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 222
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 222 (accept_3_4 16 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 222 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 222 (accept_3_4 13 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 222 (accept_3_4 10 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 222 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 222 (accept_3_4 7 77 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 222 (Polychromatic418967fa.accept_15_6_2_12_1_885 6 77 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 222
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 222 (accept_3_4 4 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 77 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 222 (accept_3_4 1 77 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 222 (allA_succ_of_accept 75 76 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 75 76 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 76 222 2 37 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 76 222
  (Polychromatic418967fa.accept_9_1_4_6_1_5 73 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 76 222 2 36 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 76 222 (accept_3_5 71 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 76 222 2 35 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 76 222 (Polychromatic418967fa.accept_12_9_4_6_1_460 69 76 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 222 2 34 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 67 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 222 2 33 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 76 222 (accept_3_5 65 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 76 222 2 32 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 76 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 76 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 76 222 2 31 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 76 222
  (Polychromatic418967fa.accept_9_7_4_6_1_273 61 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 76 222 2 30 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 76 222 (accept_3_5 59 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 76 222 2 29 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 76 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 76 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 76 222 2 28 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 76 222
  (Polychromatic418967fa.accept_9_1_4_6_1_5 55 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 76 222 2 27 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 76 222 (accept_3_5 53 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 76 222 2 26 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 76 222 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 76 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 222 2 25 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 222
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 49 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 222 2 24 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 76 222 (accept_3_5 47 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 76 222 2 23 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 76 222 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 76 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 76 222 2 22 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 76 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 76 222 2 21 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 76 222 (accept_3_5 41 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 76 222 2 20 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 76 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 76 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 222 2 19 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 222
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 76 222 2 18 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 76 222 (accept_3_5 35 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 76 222 2 17 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 76 222 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 76 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 222 2 16 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 222
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 222 2 15 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 76 222 (accept_3_5 29 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 76 222 2 14 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 76 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 76 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 76 222 2 13 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 76 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 76 222 2 12 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 76 222 (accept_3_5 23 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 76 222 2 11 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 76 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 76 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 222 2 10 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 222
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 222 2 9 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 222 (accept_3_5 17 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  222 2 8 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 222 2 7 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 76 222 (Polychromatic418967fa.accept_14_13_6_12_1_3126 13 76 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 222 2 6 38 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 222 (accept_3_5 11 76 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 222 2 5 38 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 222
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 76 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 76 222 2 4 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 76 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 76 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 222 2 3 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 222 (accept_3_5 5 76 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 76 222 2 2 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 76 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 76 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 222 2 1 38 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 76
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 222 (allA_succ_of_accept
  74 75 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 75 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 222 3 24 25 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 71 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 222 3 23 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 222 3 22 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 75 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 222 3 21 25 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 62 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 222 3 20 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 222 3 19 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 75 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 222 3 18 25 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 222 3 17 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 222 3 16 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 75 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 222 3 15 25 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 222 3 14 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 75 222 3 13 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 222 3 12 25 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 222 3 11 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 222 3 10 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 75 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 222 3 9 25 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 222 3 8 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 75 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 222 3 7 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 222 3 6 25 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 222 3 5 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 75 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 222 3 4 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 75 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 222 3 3 25 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 222 3 2 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 222
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 75 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 222 3 1 25 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 75 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 222 (allA_succ_of_accept
  73 74 222 (accept_3_4 73 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 222 2 36 37 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 222 2 35 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 74 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 74 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 222 2 34 37 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 222 (accept_3_4 67 74 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 222 2 33 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 65
  74 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 222 2 32 37 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 222
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 222 2 31 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 74 222 (accept_3_4 61 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 74 222 2 30 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 74 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 74 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 222 2 29 37 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 222 2 28 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 74 222 (accept_3_4 55 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 74 222 2 27 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 74 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 222 2 26 37 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 222 2 25 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 74 222 (accept_3_4 49 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 74 222 2 24 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 74 222 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 74 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 222 2 23 37 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 222
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 222 2 22 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 74 222 (accept_3_4 43 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 74 222 2 21 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 74 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 74 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 222 2 20 37 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 222
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 222 2 19 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 37 74 222 37 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 36 74 222 2 18 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 74 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 74 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 222 2 17 37 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 222
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 222 2 16 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 74 222 (accept_3_4 31 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 222 2 15 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 74 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 222 2 14 37 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 222
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 222 2 13 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 74 222 (accept_3_4 25 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 222 2 12 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 74 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 222 2 11 37 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 222
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 222 2 10 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 222 (accept_3_4 19 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 222 2 9 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 74 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 222 2 8 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  74 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 222 2 7 37 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 222 (accept_3_4 13
  74 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 222 2 6 37 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 222
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 74 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 74 222 2 5 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 74 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 74 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 222 2 4 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 222 (accept_3_4 7 74 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 222 2 3 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 74 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 222 2 2 37 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 74
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 222 2 1 37 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 222 (accept_3_4 1 74
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 222 (allA_succ_of_accept
  72 73 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 222 (accept_3_5 71 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 73 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 222 (Polychromatic418967fa.accept_16_5_9_14_1_5051 69 73
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 222 (accept_3_5 68 73 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 222
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 222 (accept_3_5 65 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 222 (accept_3_5 62 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 73 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 222
  (Polychromatic418967fa.accept_19_3_16_13_1_2293 60 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 222 (accept_3_5 59 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 222 (accept_3_5 56 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 73 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 222
  (Polychromatic418967fa.accept_29_25_15_19_1_13217 54 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 73 222 (accept_3_5 53 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 73 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 73 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 222 (accept_3_5 50 73 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 49
  73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 222
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 222 (accept_3_5 47 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 222 (Polychromatic418967fa.accept_13_7_8_1_1_2145 46 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 222 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 222 (accept_3_5 44 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 222
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 222 (accept_3_5 41 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 222 (accept_3_5 38 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 73 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 222
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 222 (accept_3_5 35 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 222 (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 222 (accept_3_5 32 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 222 (accept_3_5 29 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 222 (Polychromatic418967fa.accept_25_3_23_22_1_13216 28 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 222 (accept_3_5 26 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 73 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 222
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 222 (accept_3_5 23 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 222 (accept_3_5 20 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 222
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 222 (accept_3_5 17 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 222 (accept_3_5 14 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 73 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 222
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 222 (accept_3_5 11 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 222 (Polychromatic418967fa.accept_15_10_13_12_1_3384 10 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 222 (accept_3_5 8 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 222
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 222 (accept_3_5 5 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  222 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 73 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 222 (accept_3_5 2 73 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 222 (allA_succ_of_accept 71
  72 222 (Polychromatic418967fa.accept_13_6_7_1_1_335 71 72 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 72 222 2 35 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 69 72 222 3 23 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 72 222 2 34 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 72 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 222 6 11 12 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 222
  (Polychromatic418967fa.accept_17_14_4_1_1_3341 65 72 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 72 222 2 32 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 72 222 3 21 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 62 72 222 2 31 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 72 222 (Polychromatic418967fa.accept_19_4_15_13_1_13215 61 72 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 222 6 10 12 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 222
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 72 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 72 222 2 29 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 72 222 3 19 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 56 72 222 2 28 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 72 222 (Polychromatic418967fa.accept_13_3_7_1_1_334 55 72 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 222 6 9 12 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 72 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 222 2 26 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 72 222 3 17 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 72 222 2 25 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 72 222 (Polychromatic418967fa.accept_14_7_2_12_1_1430 49 72 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 222 6 8 12 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 222
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 47 72 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 72 222 2 23 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 72 222 3 15 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 72 222 2 22 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 72 222 (Polychromatic418967fa.accept_21_1_9_12_1_2719 43 72 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 222 6 7 12 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 222
  (Polychromatic418967fa.accept_21_20_9_12_1_5549 41 72 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 222 2 20 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 72 222 3 13 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 72 222 2 19 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 72 222 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 72 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 222 6 6 12 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 222
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 35 72 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 72 222 2 17 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 72 222 3 11 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 72 222 2 16 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 72 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 72 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 222 6 5 12 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 222
  (Polychromatic418967fa.accept_13_3_7_1_1_334 29 72 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 72 222 2 14 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 72 222 3 9 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 72 222 2 13 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 72 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 72 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 222 6 4 12 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 222
  (Polychromatic418967fa.accept_19_4_15_13_1_13215 23 72 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 72 222 2 11 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 72 222 3 7 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 72 222 2 10 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 222 (Polychromatic418967fa.accept_13_6_7_1_1_335 19 72 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 222 6 3 12 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 222
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 72 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 72 222 2 8 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 72 222 3 5 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 72 222 2 7 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 222 (Polychromatic418967fa.accept_21_13_9_12_1_4038 13 72 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 222 6 2 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 72 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 222 2 5 36 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 72 222 3 3 24 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 72 222 2 4 36 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 222
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 7 72 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 222 6 1 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 222 (Polychromatic418967fa.accept_17_5_4_1_1_3369 5 72 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 222 2 2 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 72 222 3 1 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 72 222 2 1 36 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 222 (Polychromatic418967fa.accept_21_1_9_12_1_2719 1 72 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 222 (allA_succ_of_accept 70
  71 222 (accept_3_4 70 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 68 71 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 222 (accept_3_4 67 71 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 65
  71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 222 (accept_3_4 64 71
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 222
  (Polychromatic418967fa.accept_10_3_1_2_1_521 63 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 71 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 62 71 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 222 (accept_3_4 61 71 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 71 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 59
  71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 222 (accept_3_4 58 71
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 222 (Polychromatic418967fa.accept_4_1_3_2_1_3
  57 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 222
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 71 222 (accept_3_4 55 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 222 (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 222 (accept_3_4 52 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 222 (Polychromatic418967fa.accept_18_15_17_6_1_4043 51 71 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 222
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 222 (accept_3_4 49 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 222 (accept_3_4 46 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 222
  (Polychromatic418967fa.accept_13_5_6_1_1_822 44 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 222 (accept_3_4 43 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 222 (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 222 (accept_3_4 40 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 71 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 222 (accept_3_4 37 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 222 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 222 (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 222 (accept_3_4 34 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 222 (accept_3_4 31 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 222 (accept_3_4 28 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 71 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 222
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 222 (accept_3_4 25 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 222 (accept_3_4 22 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 222 (accept_3_4 19 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 222 (accept_3_4 16 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 222 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 71 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 222
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 222 (accept_3_4 13 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 222 (accept_3_4 10 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 222
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 222 (accept_3_4 7 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  222 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 71 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 222 (accept_3_4 4 71 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 71 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 71
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 222 (accept_3_4 1 71 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 222 (allA_succ_of_accept 69
  70 222 (Polychromatic418967fa.accept_12_9_10_6_1_872 69 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 70 222 2 34 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 70 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 70 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 222 2 33 35 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 222 (accept_3_5 65 70 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 222 2 32 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 222
  (Polychromatic418967fa.accept_12_3_10_6_1_442 63 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 70 222 2 31 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 70 222 (Polychromatic418967fa.accept_11_6_4_2_1_599 61 70 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 222 2 30 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 222 (accept_3_5 59 70 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70 222 2 29 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 70 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 57
  70 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 222 2 28 35 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 70 222
  (Polychromatic418967fa.accept_9_1_7_6_1_75 55 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 70 222 2 27 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 70 222 (accept_3_5 53 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 70 222 2 26 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 70 222 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 70 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 222 2 25 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 222
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 70 222 2 24 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 70 222 (accept_3_5 47 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 70 222 2 23 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 70 222 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 70 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 70 222 2 22 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 222
  (Polychromatic418967fa.accept_13_4_5_1_1_833 43 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 222 2 21 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 70 222 (accept_3_5 41 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 70 222 2 20 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 70 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 70 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 222 2 19 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 222
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 222 2 18 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 70 222 (accept_3_5 35 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 70 222 2 17 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 70 222 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 70 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 222 2 16 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 222
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 70 222 2 15 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 70 222 (accept_3_5 29 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 70 222 2 14 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 70 222 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 70 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 222 2 13 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 70 222
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 70 222 2 12 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 70 222 (accept_3_5 23 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 70 222 2 11 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 70 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 70 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 222 2 10 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 222
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 222 2 9 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 222 (accept_3_5 17 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70
  222 2 8 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  70 222 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 70 222 2 7 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 70 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 70 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 222 2 6 35 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 222 (accept_3_5 11 70 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 222 2 5 35 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 222
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 70 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 222 2 4 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 222 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 70 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 222 2 3 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 222 (accept_3_5 5 70 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 70 222 2 2 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 70 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 70 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 222 2 1 35 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 70
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 222 (allA_succ_of_accept 68 69
  222 (Polychromatic418967fa.accept_12_8_9_6_1_127 68 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 69 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 69 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 222 3 22 23 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 222
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 65 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 222 3 21 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 222 (Polychromatic418967fa.accept_12_2_9_6_1_439 62
  69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 222
  (Polychromatic418967fa.accept_10_1_9_2_1_45 61 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 222 3 20 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 222 (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 69
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 222 3 19 23 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 222
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 56 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 222 3 18 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 53
  69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 222
  (Polychromatic418967fa.accept_12_4_9_6_1_440 52 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 222 3 17 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 50 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 222 (Polychromatic418967fa.accept_13_10_4_1_1_2142 49 69
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 222 3 16 23 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 222 3 15 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 222 (Polychromatic418967fa.accept_12_8_9_6_1_127 44
  69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 222 3 14 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 222 (Polychromatic418967fa.accept_10_1_9_2_1_45 41 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 222 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 69 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 222 3 13 23 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 222
  (Polychromatic418967fa.accept_12_2_9_6_1_439 38 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 222 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 222 3 12 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 222
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 222 3 11 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 222 3 10 23 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 222 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 222 3 9 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 222 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 69 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 222 3 8 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 69 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 222 3 7 23 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 222
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 222 3 6 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 222 (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 69 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 222
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 222 3 5 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 222 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 222 (Polychromatic418967fa.accept_20_13_9_2_1_5933 13 69
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 222 3 4 23 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 222 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 222 3 3 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 69 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 222 3 2 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 222 (Polychromatic418967fa.accept_13_5_4_1_1_364 5 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 69 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 222 3 1 23 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 222
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 69 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 69 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 222 (allA_succ_of_accept 67 68 222 (accept_3_4 67 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 68 222 2 33 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 68 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 65 68 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 68 222 2 32 34 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 68 222
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 68 222 2 31 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 68 222 (accept_3_4 61 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 68 222 2 30 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 68 222 (Polychromatic418967fa.accept_13_7_3_1_1_814 59 68 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 222 2 29 34 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 222
  (Polychromatic418967fa.accept_9_3_5_6_1_253 57 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 222 2 28 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 68 222 (accept_3_4 55 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 68 222 2 27 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 68 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 68 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 68 222 2 26 34 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 68 222
  (Polychromatic418967fa.accept_12_3_8_6_1_895 51 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 68 222 2 25 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 68 222 (accept_3_4 49 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 68 222 2 24 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 68 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 68 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 222 2 23 34 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 222
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 68 222 2 22 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 68 222 (accept_3_4 43 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 68 222 2 21 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 68 222 (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 68 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 222 2 20 34 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 222
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 222 2 19 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 68 222 (accept_3_4 37 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 68 222 2 18 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 68 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 68 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 222 2 17 34 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 222
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 222 2 16 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 68 222 (accept_3_4 31 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 68 222 2 15 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 68 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 68 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 222 2 14 34 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 222
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 222 2 13 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 68 222 (accept_3_4 25 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 68 222 2 12 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 68 222 (Polychromatic418967fa.accept_16_7_4_14_1_2860 23 68 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 222 2 11 34 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 222
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 222 2 10 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 68 222 (accept_3_4 19 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 68 222 2 9 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 68 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 68 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 222 2 8 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 222 (Polychromatic418967fa.accept_10_5_8_2_1_517 15
  68 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 222 2 7 34 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 222 (accept_3_4 13
  68 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 222 2 6 34 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 222
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 68 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 68 222 2 5 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 68 222 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 68 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 222 2 4 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 222 (accept_3_4 7 68 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 68 222 2 3 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 68 222 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 68 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 222 2 2 34 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 68
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 222 2 1 34 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 222 (accept_3_4 1 68
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 222 (allA_succ_of_accept 66 67
  222 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 222 (accept_3_5 65 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 222 (Polychromatic418967fa.accept_15_3_7_12_1_372 63 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 222 (accept_3_5 62 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 67 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 222
  (Polychromatic418967fa.accept_19_3_10_13_1_3482 60 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 222 (accept_3_5 59 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 222 (accept_3_5 56 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 67 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 222
  (Polychromatic418967fa.accept_10_4_7_2_1_211 54 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 222 (accept_3_5 53 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 222 (accept_3_5 50 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 222
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 222 (accept_3_5 47 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 222 (accept_3_5 44 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 67 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 222
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 42 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 222 (accept_3_5 41 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 222 (Polychromatic418967fa.accept_15_10_7_12_1_2490 40 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 222 (accept_3_5 38 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 222 (accept_3_5 35 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 222 (accept_3_5 32 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 222 (Polychromatic418967fa.accept_22_9_1_2_1_13214 31 67 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 222 (accept_3_5 29 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 222 (accept_3_5 26 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 222
  (Polychromatic418967fa.accept_10_4_7_2_1_211 24 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 222 (accept_3_5 23 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 222 (accept_3_5 20 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 67 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 222
  (Polychromatic418967fa.accept_15_3_7_12_1_372 18 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 222 (accept_3_5 17 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 222 (accept_3_5 14 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 222
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 222 (accept_3_5 11 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 222 (accept_3_5 8 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 222
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 222 (accept_3_5 5 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  222 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 67 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 67 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 222 (accept_3_5 2 67 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 222 (allA_succ_of_accept 65 66
  222 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 66 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 222 2 32 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 66 222 3 21 22 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 62 66 222 2 31 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 66 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 66 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 222 6 10 11 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 222
  (Polychromatic418967fa.accept_9_5_3_6_1_269 59 66 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 66 222 2 29 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 66 222 3 19 22 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 56 66 222 2 28 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 66 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 66 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 222 6 9 11 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 66 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 66 222 2 26 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 66 222 3 17 22 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 66 222 2 25 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 66 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 66 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 222 6 8 11 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 222
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 66 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 222 2 23 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 66 222 3 15 22 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 66 222 2 22 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 66 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 66 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 222 6 7 11 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 222
  (Polychromatic418967fa.accept_9_5_3_6_1_269 41 66 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 66 222 2 20 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 66 222 3 13 22 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 66 222 2 19 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 66 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 66 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 222 6 6 11 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 66 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 66 222 2 17 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 66 222 3 11 22 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 66 222 2 16 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 66 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 66 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 222 6 5 11 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 222
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 66 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 222 2 14 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 66 222 3 9 22 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 66 222 2 13 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 66 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 66 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 222 6 4 11 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 66 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 222 2 11 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 66 222 3 7 22 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 66 222 2 10 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 66 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 66 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 222 6 3 11 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 66 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 66 222 2 8 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 66 222 3 5 22 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 66 222 2 7 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 66 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 66 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 222 6 2 11 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 66 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 222 2 5 33 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 66 222 3 3 22 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 66 222 2 4 33 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 222
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 66 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 222 6 1 11 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 66 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 222 2 2 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 222 3 1 22 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 222 2 1 33 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 66 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 222 (allA_succ_of_accept 64 65 222
  (accept_3_4 64 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 62 65 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 222 (accept_3_4 61 65 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 222 (accept_3_4 58 65
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 222
  (Polychromatic418967fa.accept_9_3_2_6_1_264 57 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 65 222 (Polychromatic418967fa.accept_11_1_10_2_1_58 56 65 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 222 (accept_3_4 55 65 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 65 222 (Polychromatic418967fa.accept_15_9_5_12_1_1640 54 65 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 222 (accept_3_4 52 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 50 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 222 (accept_3_4 49 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 65 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 222 (accept_3_4 46 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 222 (accept_3_4 43 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 222 (Polychromatic418967fa.accept_19_4_8_13_1_7802 42 65 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 222
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 222 (accept_3_4 40 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 222 (accept_3_4 37 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 222 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 65 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 222 (accept_3_4 34 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 222 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 222 (accept_3_4 31 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 65 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 222
  (Polychromatic418967fa.accept_16_13_1_14_1_2855 29 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 222 (accept_3_4 28 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 222 (accept_3_4 25 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 65 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 222 (accept_3_4 22 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 222 (Polychromatic418967fa.accept_16_4_1_14_1_3908 20 65 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 222 (accept_3_4 19 65 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 65 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 222
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 222 (accept_3_4 16 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 222 (accept_3_4 13 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 65 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 222 (accept_3_4 10 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 222 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 222 (accept_3_4 7 65 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 222 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 65 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 222
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 222 (accept_3_4 4 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 222 (Polychromatic418967fa.accept_15_2_5_12_1_369 2 65 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 222 (accept_3_4 1 65 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 222
  (allA_succ_of_accept 63 64 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 64 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 64 222 2 31 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 64 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 61
  64 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 222 2 30 32 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 222 (accept_3_5 59
  64 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 222 2 29 32 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 222
  (Polychromatic418967fa.accept_9_3_1_6_1_86 57 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 222 2 28 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 64 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 64 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 222 2 27 32 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 222 (accept_3_5 53 64 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 222 2 26 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 222 (Polychromatic418967fa.accept_11_7_9_2_1_260 51
  64 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 222 2 25 32 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 222
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 222 2 24 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 64 222 (accept_3_5 47 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 64 222 2 23 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 64 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 64 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 64 222 2 22 32 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 64 222
  (Polychromatic418967fa.accept_9_7_1_6_1_261 43 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 64 222 2 21 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 64 222 (accept_3_5 41 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 64 222 2 20 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 64 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 64 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 222 2 19 32 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 222
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 222 2 18 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 64 222 (accept_3_5 35 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 64 222 2 17 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 64 222 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 64 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 222 2 16 32 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 222 2 15 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 64 222 (accept_3_5 29 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 64 222 2 14 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 64 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 64 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 222 2 13 32 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 222 2 12 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 64 222 (accept_3_5 23 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 64 222 2 11 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 64 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 222 2 10 32 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 222
  (Polychromatic418967fa.accept_17_2_13_1_1_3355 19 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 222 2 9 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 222 (accept_3_5 17 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  222 2 8 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 222 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 222 2 7 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 64 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 64 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 222 2 6 32 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 222 (accept_3_5 11 64 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 222 2 5 32 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 222
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 64 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 222 2 4 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 64 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 222 2 3 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 222 (accept_3_5 5 64 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 222 2 2 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 64 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 222 2 1 32 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 222 (Polychromatic418967fa.accept_15_1_4_12_1_2401 1
  64 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 222 (allA_succ_of_accept 62 63 222
  (Polychromatic418967fa.accept_12_2_3_6_1_112 62 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 222 3 20 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 222 (Polychromatic418967fa.accept_13_7_11_1_1_2903
  59 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 222
  (Polychromatic418967fa.accept_12_10_3_6_1_882 58 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 222 3 19 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 56 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 222 (Polychromatic418967fa.accept_10_5_3_2_1_899 55 63 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 222 3 18 21 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 222 (Polychromatic418967fa.accept_12_4_3_6_1_879 52 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 222 3 17 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 222 (Polychromatic418967fa.accept_12_2_3_6_1_112 50
  63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 63 222 3 16 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 222 (Polychromatic418967fa.accept_13_8_11_1_1_3789 47 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 222 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 63 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 222 3 15 21 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 222
  (Polychromatic418967fa.accept_12_8_3_6_1_909 44 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 222 (Polychromatic418967fa.accept_15_13_3_12_1_1609 43 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 222 3 14 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 222
  (Polychromatic418967fa.accept_12_4_3_6_1_879 40 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 63 222 3 13 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 63 222 (Polychromatic418967fa.accept_11_5_8_2_1_588 38 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 222 3 12 21 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 222
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 222 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 222 3 11 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 32
  63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 222
  (Polychromatic418967fa.accept_10_1_3_2_1_220 31 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 222 3 10 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 222 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 63 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 222 3 9 21 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 222
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 222 3 8 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 222 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 63
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 222
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 222 3 7 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 222 (Polychromatic418967fa.accept_14_5_7_12_1_4006 19 63
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 222 3 6 21 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 222 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 222 3 5 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 222 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 63 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 222 3 4 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 222 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 222 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 63 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 222 3 3 21 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 222
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 222 (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 222 3 2 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 222
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 63 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 222 3 1 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 222 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 63 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 222 (allA_succ_of_accept 61 62 222
  (accept_3_4 61 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 222 2 30 31 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 222
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 222 2 29 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 62 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 62 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 222 2 28 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 222 (accept_3_4 55 62 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 222 2 27 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 53
  62 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 222 2 26 31 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 222
  (Polychromatic418967fa.accept_12_3_2_6_1_138 51 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 222 2 25 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 62 222 (accept_3_4 49 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 62 222 2 24 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 62 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 62 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 222 2 23 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 222
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 222 2 22 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 222 (accept_3_4 43 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 222 2 21 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 62 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 222 2 20 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 222 2 19 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 222 (accept_3_4 37 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 222 2 18 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 222 (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 62 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 222 2 17 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 222
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 222 2 16 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 62 222 (accept_3_4 31 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 62 222 2 15 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 62 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 222 2 14 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 222
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 222 2 13 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 62 222 (accept_3_4 25 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 222 2 12 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 62 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 222 2 11 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 222
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 222 2 10 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 222 (accept_3_4 19 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 222 2 9 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 222 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 62 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 222 2 8 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  62 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 222 2 7 31 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 222 (accept_3_4 13
  62 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 222 2 6 31 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 62 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 222 2 5 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 222 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 62 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 222 2 4 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 222 (accept_3_4 7 62 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 222 2 3 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 62 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 222 2 2 31 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 62
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 222 2 1 31 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 222 (accept_3_4 1 62
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 222 (allA_succ_of_accept 60 61 222
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 60 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 222 (accept_3_5 59 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 222 (accept_3_5 56 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 222
  (Polychromatic418967fa.accept_13_2_9_1_1_67 54 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 222 (accept_3_5 53 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 222 (Polychromatic418967fa.accept_14_10_5_12_1_3995 52 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 222 (accept_3_5 50 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 61 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 222
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 222 (accept_3_5 47 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 222 (Polychromatic418967fa.accept_13_6_9_1_1_5604 45 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 222 (accept_3_5 44 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 222
  (Polychromatic418967fa.accept_16_10_13_14_1_5042 42 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 61 222 (accept_3_5 41 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 61 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 61 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 222 (accept_3_5 38 61 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 37
  61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 222
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 222 (accept_3_5 35 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 222 (Polychromatic418967fa.accept_13_8_9_1_1_2147 34 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 222 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 222 (accept_3_5 32 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 222
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 222 (accept_3_5 29 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 222 (accept_3_5 26 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 222 (Polychromatic418967fa.accept_19_6_4_13_1_2329 25 61 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 222
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 222 (accept_3_5 23 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 222 (accept_3_5 20 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 222
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 222 (accept_3_5 17 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 222 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 222 (accept_3_5 14 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 61 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 222
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 222 (accept_3_5 11 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 222 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 222 (accept_3_5 8 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 222
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 222 (accept_3_5 5 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  222 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 61 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 222 (accept_3_5 2 61 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 61 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 222 (allA_succ_of_accept 59 60 222 (Polychromatic418967fa.accept_13_7_8_1_1_2145 59 60 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 222 2 29 30 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 60 222 3 19 20 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 60 222 2 28 30 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 222
  (Polychromatic418967fa.accept_7_6_4_5_1_314 55 60 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 60 222 6 9 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 60 222 (Polychromatic418967fa.accept_21_11_18_12_1_1494 53 60 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 222 2 26 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 60 222 3 17 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 60 222 2 25 30 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 222
  (Polychromatic418967fa.accept_17_15_9_1_1_3363 49 60 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 222 6 8 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 222 (Polychromatic418967fa.accept_19_9_3_13_1_2300 47 60 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 222 2 23 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 222 3 15 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 222 2 22 30 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 60 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 222 6 7 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 60 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 222 2 20 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 222 3 13 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 60 222 2 19 30 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 60 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 222 6 6 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 60 222 (Polychromatic418967fa.accept_13_9_8_1_1_824 35 60 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 222 2 17 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 60 222 3 11 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 60 222 2 16 30 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 222
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 60 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 222 6 5 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 60 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 222 2 14 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 222 3 9 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 60 222 2 13 30 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 222
  (Polychromatic418967fa.accept_13_12_8_1_1_825 25 60 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 222 6 4 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 60 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 222 2 11 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 222 3 7 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 222 2 10 30 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 222
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 60 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 222 6 3 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 222 (Polychromatic418967fa.accept_24_17_12_6_1_6190 17 60 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 222 2 8 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 222 3 5 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 222 2 7 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 13
  60 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 222 6 2 10 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 222
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 60 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 222 2 5 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 60 222 3 3 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 60 222 2 4 30 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 222 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 60 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 222 6 1 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 222 (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 60 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 222 2 2 30 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 222 3 1 20 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 222 2 1 30 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 222 (allA_succ_of_accept 58
  59 222 (accept_3_4 58 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 56 59 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 222 (accept_3_4 55 59 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 222 (Polychromatic418967fa.accept_15_9_14_12_1_913 54 59 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 222 (accept_3_4 52 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 222 (accept_3_4 49 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 59 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 222
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 222 (accept_3_4 46 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 222 (accept_3_4 43 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 222 (Polychromatic418967fa.accept_11_9_4_2_1_600 42 59 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 222 (accept_3_4 40 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 222 (accept_3_4 37 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 59 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 222
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 222 (accept_3_4 34 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 222 (Polychromatic418967fa.accept_13_6_7_1_1_335 32 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 222 (accept_3_4 31 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 59 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 222 (accept_3_4 28 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 222 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 222 (accept_3_4 25 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 222 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 59 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 222 (accept_3_4 22 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 222 (accept_3_4 19 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 222 (Polychromatic418967fa.accept_24_18_11_6_1_8079 18 59 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 222 (accept_3_4 16 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 222 (Polychromatic418967fa.accept_25_14_9_22_1_13213 14 59 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 222 (accept_3_4 13 59 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 59 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 222
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 222 (accept_3_4 10 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 59 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 222 (accept_3_4 7 59 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 222 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 59 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 222 (accept_3_4 4 59 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 222 (accept_3_4 1 59 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 222 (allA_succ_of_accept 57 58 222
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 222 2 28 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 58 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 58 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 222 2 27 29 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 222 (accept_3_5 53 58 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 222 2 26 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 222 (Polychromatic418967fa.accept_12_3_10_6_1_442
  51 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 222 2 25 29 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 222
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 49 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 222 2 24 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 58 222 (accept_3_5 47 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 58 222 2 23 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 58 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 58 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 222 2 22 29 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 222
  (Polychromatic418967fa.accept_9_7_4_6_1_273 43 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 222 2 21 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 58 222 (accept_3_5 41 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 58 222 2 20 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 58 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 58 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 222 2 19 29 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 222
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 222 2 18 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 58 222 (accept_3_5 35 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 58 222 2 17 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 58 222 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 58 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 222 2 16 29 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 222
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 222 2 15 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 58 222 (accept_3_5 29 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 58 222 2 14 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 58 222 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 58 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 222 2 13 29 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 222 2 12 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 58 222 (accept_3_5 23 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 58 222 2 11 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 58 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 58 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 222 2 10 29 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 222
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 222 2 9 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 222 (accept_3_5 17 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  222 2 8 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 222 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 222 2 7 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 58 222 (Polychromatic418967fa.accept_16_13_10_14_1_2871 13 58 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 222 2 6 29 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 222 (accept_3_5 11 58 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 222 2 5 29 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 222
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 58 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 222 2 4 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 58 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 222 2 3 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 222 (accept_3_5 5 58 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 222 2 2 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 58 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 222 2 1 29 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 58
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 222 (allA_succ_of_accept 56 57 222
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 222 3 18 19 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 53
  57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 52 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 222 3 17 19 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 57 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 222 3 16 19 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 222 3 15 19 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 222 (Polychromatic418967fa.accept_9_8_3_6_1_533 44
  57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 222 3 14 19 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 57 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 222 3 13 19 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 222 3 12 19 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 34 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 222 3 11 19 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 222 3 10 19 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 222
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 222 3 9 19 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 222 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 57 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 222 3 8 19 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 57 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 222 3 7 19 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 222 3 6 19 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 57 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 222
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 222 3 5 19 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 57 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 222 3 4 19 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 222 3 3 19 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 222 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 222 3 2 19 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 57 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 222 3 1 19 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 222
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 57 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 222))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 222 (allA_succ_of_accept 55 56 222 (accept_3_4 55 56 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  54 56 222 2 27 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 56 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 222 2 26 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 222 (Polychromatic418967fa.accept_10_1_6_2_1_867 51
  56 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 222 2 25 28 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 222 (accept_3_4 49
  56 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 222 2 24 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 222
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 47 56 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 222 2 23 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 56 222 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 56 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 222 2 22 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 222 (accept_3_4 43 56 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 222 2 21 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 41
  56 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 222 2 20 28 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 222
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 222 2 19 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 56 222 (accept_3_4 37 56 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 56 222 2 18 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 56 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 56 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 222 2 17 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 222
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 56 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 222 2 16 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 56 222 (accept_3_4 31 56 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 56 222 2 15 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 56 222 (Polychromatic418967fa.accept_13_3_4_1_1_363 29 56 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 222 2 14 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 222
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 56 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 56 222 2 13 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 56 222 (accept_3_4 25 56 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 56 222 2 12 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 56 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 56 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 222 2 11 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 222
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 222 2 10 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 56 222 (accept_3_4 19 56 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 56 222 2 9 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 56 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 56 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 222 2 8 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 222 (Polychromatic418967fa.accept_12_3_8_6_1_895 15
  56 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 222 2 7 28 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 222 (accept_3_4 13
  56 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 222 2 6 28 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 222
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 56 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 56 222 2 5 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 56 222 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 56 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 222 2 4 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 222 (accept_3_4 7 56 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 56 222 2 3 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 56 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 56 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 222 2 2 28 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 222 2 1 28 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 222 (accept_3_4 1 56
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 222))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 222 (allA_succ_of_accept 54 55 222 (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 55 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 222 (accept_3_5 53 55 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 55 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 222
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 51 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 222 (accept_3_5 50 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 55 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 222 (accept_3_5 47 55 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 55 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 222 (accept_3_5 44 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 222 (Polychromatic418967fa.accept_16_10_7_14_1_2882 42 55 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 222 (accept_3_5 41 55 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 55 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 222 (accept_3_5 38 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 55 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 222 (accept_3_5 35 55 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 55 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 222 (accept_3_5 32 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 55 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 222 (accept_3_5 29 55 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 222 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 55 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 222
  (Polychromatic418967fa.accept_10_7_5_2_1_880 27 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 222 (accept_3_5 26 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 222 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 55 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 222 (accept_3_5 23 55 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 55 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 222 (accept_3_5 20 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 222 (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 55 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 222 (accept_3_5 17 55 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 55 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 222 (accept_3_5 14 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 55 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 222 (accept_3_5 11 55 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 222 (Polychromatic418967fa.accept_16_10_7_14_1_2882 10 55 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 222 (accept_3_5 8 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  222 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 222 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 55 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 222 (accept_3_5 5 55 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 55 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 55
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 222 (accept_3_5 2 55 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  222))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 222 (allA_succ_of_accept 53 54 222
  (Polychromatic418967fa.accept_17_2_3_1_1_2244 53 54 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 222 2 26 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 54 222 3 17 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 54 222 2 25 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 54 222 (Polychromatic418967fa.accept_15_4_9_12_1_2495 49 54 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 222 6 8 9 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 222
  (Polychromatic418967fa.accept_10_7_4_2_1_903 47 54 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 222 2 23 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 54 222 3 15 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 54 222 2 22 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 54 222 (Polychromatic418967fa.accept_17_9_3_1_1_2275 43 54 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 222 6 7 9 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 222
  (Polychromatic418967fa.accept_19_3_16_13_1_2293 41 54 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 222 2 20 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 54 222 3 13 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 54 222 2 19 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 54 222 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 54 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 222 6 6 9 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 222
  (Polychromatic418967fa.accept_13_9_2_1_1_813 35 54 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 222 2 17 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 54 222 3 11 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 54 222 2 16 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 54 222 (Polychromatic418967fa.accept_19_12_16_13_1_9123 31 54 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 222 6 5 9 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 222
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 54 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 222 2 14 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 54 222 3 9 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 54 222 2 13 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 54 222 (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 54 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 222 6 4 9 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 222
  (Polychromatic418967fa.accept_11_1_10_2_1_58 23 54 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 222 2 11 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 54 222 3 7 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 54 222 2 10 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 54 222 (Polychromatic418967fa.accept_13_6_2_1_1_2137 19 54 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 222 6 3 9 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 222
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 54 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 54 222 2 8 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 54 222 3 5 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 54 222 2 7 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 222 (Polychromatic418967fa.accept_22_13_10_2_1_5206 13 54 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 222 6 2 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 222 (Polychromatic418967fa.accept_19_11_16_13_1_4853 11 54
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 222 2 5 27 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 222 3 3 18 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 222 2 4 27 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 222
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 54 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 222 6 1 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 222 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 54 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 222 2 2 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 54 222 3 1 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 54 222 2 1 27 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 222 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 54 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 222 (allA_succ_of_accept 52 53 222 (accept_3_4
  52 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 53 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 222 (accept_3_4 49 53 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 53 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 222 (accept_3_4 46 53
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 222
  (Polychromatic418967fa.accept_10_5_3_2_1_899 45 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 53 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 222 (accept_3_4 43 53 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 222 (Polychromatic418967fa.accept_16_10_5_14_1_6173 42 53 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 222
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 222 (accept_3_4 40 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 53 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 222 (accept_3_4 37 53 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 53 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 222 (accept_3_4 34 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 222 (Polychromatic418967fa.accept_15_3_8_12_1_900 33 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 53 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 222 (accept_3_4 31 53 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 53 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 222 (accept_3_4 28 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 222 (Polychromatic418967fa.accept_11_4_9_2_1_259 26 53 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 222 (accept_3_4 25 53 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 222 (Polychromatic418967fa.accept_21_3_11_12_1_10183 24 53 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 222 (accept_3_4 22 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 53 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 222 (accept_3_4 19 53 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 222 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 53 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 222
  (Polychromatic418967fa.accept_19_17_15_13_1_7794 17 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 53 222 (accept_3_4 16 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 53 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 53 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 222 (accept_3_4 13 53 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 12
  53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 222 (accept_3_4 10 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 53 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 222 (accept_3_4 7 53 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 53 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 222
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 222 (accept_3_4 4 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 53 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 222 (accept_3_4 1 53 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 222))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 222
  (allA_succ_of_accept 51 52 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 52 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 222 2 25 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 49
  52 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 222 2 24 26 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 222 (accept_3_5 47
  52 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 222 2 23 26 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 222
  (Polychromatic418967fa.accept_12_9_4_6_1_460 45 52 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 52 222 2 22 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 52 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 52 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 222 2 21 26 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 222 (accept_3_5 41 52 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 222 2 20 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 39
  52 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 222 2 19 26 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 52 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 222 2 18 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 52 222 (accept_3_5 35 52 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 52 222 2 17 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 52 222 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 52 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 222 2 16 26 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 222
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 52 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 222 2 15 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 52 222 (accept_3_5 29 52 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 52 222 2 14 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 52 222 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 52 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 222 2 13 26 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 222
  (Polychromatic418967fa.accept_15_10_7_12_1_2490 25 52 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 222 2 12 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 52 222 (accept_3_5 23 52 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 52 222 2 11 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 52 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 52 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 222 2 10 26 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 222
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 52 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 222 2 9 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 222 (accept_3_5 17 52 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  222 2 8 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 52 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 222 2 7 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 52 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 52 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 222 2 6 26 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 222 (accept_3_5 11 52 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 222 2 5 26 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 52 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 52 222 2 4 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 52 222 (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 52 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 222 2 3 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 222 (accept_3_5 5 52 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 52 222 2 2 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 52 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 222 2 1 26 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 52
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  222)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 222 (allA_succ_of_accept 50 51 222
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 222 3 16 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 222 (Polychromatic418967fa.accept_13_8_12_1_1_4662
  47 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 46 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 222 3 15 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 51 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 222 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 51 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 222 3 14 17 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 222 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 51 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 222 3 13 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 38
  51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 222 3 12 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 222 (Polychromatic418967fa.accept_14_7_9_12_1_3975 35 51 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 222 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 51 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 222 3 11 17 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 51 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 222 3 10 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 222
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 222 3 9 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 222 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 51 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 222 3 8 17 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 222
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 222 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 51 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 222 3 7 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 222 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 51 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 222
  (Polychromatic418967fa.accept_10_9_1_2_1_522 19 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 222 3 6 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 222 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 51 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 222 3 5 17 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 222
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 222 3 4 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 51 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 222
  (Polychromatic418967fa.accept_7_3_2_5_1_147 10 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 222 3 3 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 51 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 222 (Polychromatic418967fa.accept_14_7_9_12_1_3975 7 51 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 222 3 2 17 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 51 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 222 3 1 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 222 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 51 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 222))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 222 (allA_succ_of_accept 49 50 222
  (accept_3_4 49 50 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 222 2 24 25 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 222
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 50 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 222 2 23 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 50 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 50 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 222 2 22 25 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 222 (accept_3_4 43 50 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 222 2 21 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 41
  50 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 222 2 20 25 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 50 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 222 2 19 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 50 222 (accept_3_4 37 50 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 50 222 2 18 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 50 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 50 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 222 2 17 25 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 222
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 50 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 222 2 16 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 50 222 (accept_3_4 31 50 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 50 222 2 15 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 50 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 222 2 14 25 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 50 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 50 222 2 13 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 50 222 (accept_3_4 25 50 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 50 222 2 12 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 222 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 50 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 222 2 11 25 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 222
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 50 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 222 2 10 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 222 (accept_3_4 19 50 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 50 222 2 9 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 50 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 50 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 222 2 8 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 222 (Polychromatic418967fa.accept_11_4_6_2_1_51 15
  50 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 222 2 7 25 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 222 (accept_3_4 13
  50 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 222 2 6 25 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 50 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 222 2 5 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 222 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 50 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 222 2 4 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 222 (accept_3_4 7 50 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 222 2 3 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 222 (Polychromatic418967fa.accept_17_5_16_1_1_3358 5 50 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 222 2 2 25 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 50
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 222 2 1 25 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 222 (accept_3_4 1 50
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 222))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 222 (allA_succ_of_accept 48 49 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 49 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 222 (accept_3_5 47 49 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 49 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 222
  (Polychromatic418967fa.accept_16_13_1_14_1_2855 45 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 222 (accept_3_5 44 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 222 (Polychromatic418967fa.accept_24_18_1_6_1_11510 42 49 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 222 (accept_3_5 41 49 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 222 (Polychromatic418967fa.accept_19_2_11_13_1_9180 40 49
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 222 (accept_3_5 38 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 222 (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 49 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 222 (accept_3_5 35 49 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 49 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 222
  (Polychromatic418967fa.accept_14_5_7_12_1_4006 33 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 222 (accept_3_5 32 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 49 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 222 (accept_3_5 29 49 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 49 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 222 (accept_3_5 26 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 222 (Polychromatic418967fa.accept_13_11_10_1_1_1409 24 49 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 222 (accept_3_5 23 49 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 222 (Polychromatic418967fa.accept_13_9_10_1_1_1389 22 49
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 222
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 222 (accept_3_5 20 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 222 (Polychromatic418967fa.accept_21_18_7_12_1_10175 18 49 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 222 (accept_3_5 17 49 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 49 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 222 (accept_3_5 14 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 222 (Polychromatic418967fa.accept_16_13_1_14_1_2855 13 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 49 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 222 (accept_3_5 11 49 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 49 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 222
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 222 (accept_3_5 8 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 222 (Polychromatic418967fa.accept_19_6_11_13_1_4842 6 49 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 222 (accept_3_5 5 49 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 222 (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 49 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 222 (accept_3_5 2 49 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  222))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 222 (allA_succ_of_accept 47 48 222
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 48 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 222 2 23 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 48 222 3 15 16 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 48 222 2 22 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 48 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 48 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 222 6 7 8 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 222
  (Polychromatic418967fa.accept_9_5_3_6_1_269 41 48 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 222 2 20 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 48 222 3 13 16 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 48 222 2 19 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 48 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 48 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 222 6 6 8 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 48 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 222 2 17 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 48 222 3 11 16 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 48 222 2 16 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 48 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 48 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 222 6 5 8 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 48 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 222 2 14 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 48 222 3 9 16 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 48 222 2 13 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 48 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 222 6 4 8 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 222
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 48 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 48 222 2 11 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 48 222 3 7 16 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 48 222 2 10 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 48 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 48 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 222 6 3 8 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 222
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 48 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 48 222 2 8 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 48 222 3 5 16 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 48 222 2 7 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 222 6 2 8 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 48 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 222 2 5 24 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 48 222 3 3 16 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 48 222 2 4 24 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 222
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 222 6 1 8 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 48 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 222 2 2 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 222 3 1 16 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 222 2 1 24 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  222)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 222 (allA_succ_of_accept 46 47 222 (accept_3_4 46 47
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 222 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 222
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 222 (accept_3_4 43 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 222 (Polychromatic418967fa.accept_16_10_15_14_1_1086 42 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 222 (accept_3_4 40 47 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 47 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 222
  (Polychromatic418967fa.accept_13_12_8_1_1_825 38 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 222 (accept_3_4 37 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 222 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 47 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 222 (accept_3_4 34 47 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 222
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 222 (accept_3_4 31 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 222 (accept_3_4 28 47 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 222 (Polychromatic418967fa.accept_21_6_5_12_1_10314 27 47 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 222
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 222 (accept_3_4 25 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 222 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 47 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 222 (accept_3_4 22 47 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 222
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 20 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 222 (accept_3_4 19 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 222 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 222 (accept_3_4 16 47 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 222 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 47 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 222
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 222 (accept_3_4 13 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 222 (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 47 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 222 (accept_3_4 10 47 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 222
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 222 (accept_3_4 7 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  222 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 47 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 222 (accept_3_4 4 47 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 47 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 222
  (Polychromatic418967fa.accept_17_2_13_1_1_3355 2 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 222 (accept_3_4 1 47 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  222))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 222 (allA_succ_of_accept 45 46 222
  (Polychromatic418967fa.accept_12_9_10_6_1_872 45 46 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 222 2 22 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 46 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 46 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 222 2 21 23 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 222 (accept_3_5 41 46 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 222 2 20 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 39
  46 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 222 2 19 23 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 46 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 222 2 18 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 46 222 (accept_3_5 35 46 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 46 222 2 17 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 46 222 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 46 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 222 2 16 23 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 222
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 46 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 222 2 15 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 46 222 (accept_3_5 29 46 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 46 222 2 14 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 46 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 222 2 13 23 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 222
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 46 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 46 222 2 12 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 46 222 (accept_3_5 23 46 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 46 222 2 11 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 46 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 46 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 222 2 10 23 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 222
  (Polychromatic418967fa.accept_13_6_7_1_1_335 19 46 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 222 2 9 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 222 (accept_3_5 17 46 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  222 2 8 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 46 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 222 2 7 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 46 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 46 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 222 2 6 23 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 222 (accept_3_5 11 46 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 222 2 5 23 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 46 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 222 2 4 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 46 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 222 2 3 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 222 (accept_3_5 5 46 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 222 2 2 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 46 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 222 2 1 23 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 46
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  222)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 222 (allA_succ_of_accept 44 45 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 45 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 222 3 14 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 222 (Polychromatic418967fa.accept_13_2_6_1_1_3807
  41 45 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 222
  (Polychromatic418967fa.accept_12_4_9_6_1_440 40 45 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 222 3 13 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 222 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 45 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 45 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 222 3 12 15 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 222 (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 45 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 222 3 11 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 222 (Polychromatic418967fa.accept_11_10_1_2_1_1624
  32 45 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 222 3 10 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 45 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 222 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 45 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 222 3 9 15 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 222
  (Polychromatic418967fa.accept_12_2_9_6_1_439 26 45 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 222 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 45 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 222 3 8 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 222
  (Polychromatic418967fa.accept_7_1_3_5_1_33 22 45 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 222 3 7 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 222 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 45 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 222 3 6 15 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 222
  (Polychromatic418967fa.accept_10_7_5_2_1_880 17 45 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 45 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 222 3 5 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 222 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 45 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 222
  (Polychromatic418967fa.accept_10_3_5_2_1_38 13 45 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 222 3 4 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 222 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 45
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 222 3 3 15 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 222
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 45 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 222 3 2 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 222 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 45 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 222
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 45 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 222 3 1 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 45 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 45 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  222))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 222 (allA_succ_of_accept 43 44 222 (accept_3_4 43 44
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 222 2 21 22 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 222
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 44 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 222 2 20 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 44 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 44 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 222 2 19 22 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 222 (accept_3_4 37 44 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 222 2 18 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 222 (Polychromatic418967fa.accept_13_9_5_1_1_1382
  35 44 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 222 2 17 22 111
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 222
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 44 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 222 2 16 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 44 222 (accept_3_4 31 44 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 44 222 2 15 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 44 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 44 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 222 2 14 22 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 222
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 44 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 222 2 13 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 44 222 (accept_3_4 25 44 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 44 222 2 12 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 44 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 44 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 222 2 11 22 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 222
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 222 2 10 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 44 222 (accept_3_4 19 44 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 44 222 2 9 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 44 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 44 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 222 2 8 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 222 (Polychromatic418967fa.accept_12_3_8_6_1_895 15
  44 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 222 2 7 22 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 222 (accept_3_4 13
  44 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 222 2 6 22 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 44 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 44 222 2 5 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 44 222 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 44 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 222 2 4 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 222 (accept_3_4 7 44 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 44 222 2 3 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 44 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 44 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 222 2 2 22 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 44
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 222 2 1 22 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 222 (accept_3_4 1 44
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 222)))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  43 222 (allA_succ_of_accept 42 43 222 (Polychromatic418967fa.accept_13_3_4_1_1_363 42 43 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 222 (accept_3_5 41 43 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 43 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 222 (accept_3_5 38 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 222 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 43 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 222 (accept_3_5 35 43 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 43 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 222 (accept_3_5 32 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 43 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 222 (accept_3_5 29 43 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 43 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 222 (accept_3_5 26 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 222 (accept_3_5 23 43 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 43 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 222 (accept_3_5 20 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 43 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 222 (accept_3_5 17 43 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 222 (Polychromatic418967fa.accept_13_3_4_1_1_363 16 43 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 222
  (Polychromatic418967fa.accept_10_5_3_2_1_899 15 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 222 (accept_3_5 14 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 43 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 222 (accept_3_5 11 43 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 43 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 222 (accept_3_5 8 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  222 (Polychromatic418967fa.accept_19_7_5_13_1_3493 7 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 43 222 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 43 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 222 (accept_3_5 5 43 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 43 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 222 (accept_3_5 2 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43
  222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 43 222))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 222 (allA_succ_of_accept 41 42 222
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 42 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 222 2 20 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 42 222 3 13 14 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 42 222 2 19 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 42 222 (Polychromatic418967fa.accept_11_4_9_2_1_259 37 42 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 222 6 6 7 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 222
  (Polychromatic418967fa.accept_24_11_18_6_1_11499 35 42 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 42 222 2 17 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 42 222 3 11 14 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 42 222 2 16 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 222 (Polychromatic418967fa.accept_13_5_3_1_1_1398 31 42 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 222 6 5 7 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 222
  (Polychromatic418967fa.accept_11_7_9_2_1_260 29 42 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 222 2 14 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 42 222 3 9 14 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 42 222 2 13 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 42 222 (Polychromatic418967fa.accept_19_6_4_13_1_2329 25 42 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 222 6 4 7 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 222
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 23 42 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 222 2 11 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 42 222 3 7 14 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 42 222 2 10 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 42 222 (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 42 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 222 6 3 7 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 222
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 42 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 222 2 8 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 42 222 3 5 14 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 222 2 7 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 222 (Polychromatic418967fa.accept_16_13_10_14_1_2871 13 42 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 222 6 2 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 222 (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 42 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 222 2 5 21 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 222 3 3 14 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 222 2 4 21 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 222
  (Polychromatic418967fa.accept_11_7_9_2_1_260 7 42 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 222 6 1 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 222 (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 42 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 222 2 2 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 222 3 1 14 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 222 2 1 21 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 222 (Polychromatic418967fa.accept_23_1_19_15_1_11644 1 42 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  222)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 222 (allA_succ_of_accept 40 41 222 (accept_3_4 40 41 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 222
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 222 (accept_3_4 37 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 222 (accept_3_4 34 41 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 222 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 41 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 222 (accept_3_4 31 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 41 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 222 (accept_3_4 28 41 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 222
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 222 (accept_3_4 25 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 222 (Polychromatic418967fa.accept_21_3_20_12_1_10252 24 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 222 (accept_3_4 22 41 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 222
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 222 (accept_3_4 19 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 41 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 222 (accept_3_4 16 41 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 222
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 41 222 (accept_3_4 13 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 41 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 41 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 222 (accept_3_4 10 41 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 222 (Polychromatic418967fa.accept_10_9_1_2_1_522 9
  41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 222 (accept_3_4 7 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  222 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 222 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 41 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 222 (accept_3_4 4 41 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  41 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 222 (accept_3_4 1 41 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 222))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 222
  (allA_succ_of_accept 39 40 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 40 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 222 2 19 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 40
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 222 2 18 20 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 222 (accept_3_5 35
  40 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 222 2 17 20 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 222
  (Polychromatic418967fa.accept_12_9_4_6_1_460 33 40 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 40 222 2 16 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 40 222 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 40 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 222 2 15 20 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 222 (accept_3_5 29 40 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 222 2 14 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 40 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 27
  40 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 222 2 13 20 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 222
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 40 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 40 222 2 12 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 40 222 (accept_3_5 23 40 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 40 222 2 11 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 40 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 222 2 10 20 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 222
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 40 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 40 222 2 9 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 40 222 (accept_3_5 17 40 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40
  222 2 8 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  40 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 40 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 40 222 2 7 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 40 222 (Polychromatic418967fa.accept_15_13_10_12_1_2503 13 40 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 222 2 6 20 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 222 (accept_3_5 11 40 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 222 2 5 20 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 222
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 40 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 222 2 4 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 40 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 222 2 3 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 222 (accept_3_5 5 40 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 222 2 2 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 40 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 222 2 1 20 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 40
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  222)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 222 (allA_succ_of_accept 38 39 222
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 39 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 222 3 12 13 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 222 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  39 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 222
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 39 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 222 3 11 13 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 39 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 222 3 10 13 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 222 3 9 13 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 222 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 39 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 222 3 8 13 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 39 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 39 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 222 3 7 13 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 222
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 39 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 39 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 222 3 6 13 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 39 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 222 3 5 13 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 39 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 222 3 4 13 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 222
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 39 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 222 3 3 13 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 39 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 222
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 222 3 2 13 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 222 3 1 13 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 222
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 39 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 222))))))))))))))))))))))))))))))))))))))) (allB_succ 38 222
  (allA_succ_of_accept 37 38 222 (accept_3_4 37 38 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  222 2 18 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 38 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 38 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 222 2 17 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 222 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 38 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 222 2 16 19 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 222 (accept_3_4 31 38 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 222 2 15 19 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 222
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 38 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 222 2 14 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 38 222 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 38 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 222 2 13 19 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 222 (accept_3_4 25 38 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 222 2 12 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 23
  38 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 222 2 11 19 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 222
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 38 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 222 2 10 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 38 222 (accept_3_4 19 38 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 38 222 2 9 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 38 222 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 38 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 222 2 8 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  38 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 222 2 7 19 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 222 (accept_3_4 13
  38 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 222 2 6 19 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 222
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 38 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 222 2 5 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 38 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 222 2 4 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 222 (accept_3_4 7 38 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 222 2 3 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 38 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 222 2 2 19 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 38
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 222 2 1 19 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 222 (accept_3_4 1 38
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 222)))))))))))))))))))))))))))))))))))))) (allB_succ 37 222
  (allA_succ_of_accept 36 37 222 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 37 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 222 (accept_3_5 35 37 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 37 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 222 (Polychromatic418967fa.accept_13_7_11_1_1_2903
  33 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 222 (accept_3_5 32
  37 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 37 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 222 (accept_3_5 29 37 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 222 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 37 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  37 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 222 (accept_3_5 26 37
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 222 (accept_3_5 23 37 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 37 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  37 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 222 (accept_3_5 20 37
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 222 (Polychromatic418967fa.accept_4_3_1_2_1_62
  19 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 222 (accept_3_5 17 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 222 (accept_3_5 14 37 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 222 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 37 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 222
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 222 (accept_3_5 11 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 222 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 37 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 222 (accept_3_5 8 37 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 222
  (Polychromatic418967fa.accept_11_6_4_2_1_599 6 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 222 (accept_3_5 5 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  222 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 37 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 222 (accept_3_5 2 37 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 222 (Polychromatic418967fa.accept_19_1_18_13_1_7796 1 37 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 222))))))))))))))))))))))))))))))))))))) (allB_succ 36 222
  (allA_succ_of_accept 35 36 222 (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 36 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 222 2 17 18 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 222 3 11 12 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 222 2 16 18 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 222 6 5 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 222 (Polychromatic418967fa.accept_21_8_15_12_1_5474 29 36 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 222 2 14 18 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 36 222 3 9 12 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 36 222 2 13 18 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 222
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 222 6 4 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 222 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 36 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 222 2 11 18 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 222 3 7 12 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 222 2 10 18 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 222
  (Polychromatic418967fa.accept_21_19_15_12_1_5523 19 36 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 36 222 6 3 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 36 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 222 2 8 18 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 222 3 5 12 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 222 2 7 18 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 222 6 2 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 222 2 5 18 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 36 222 3 3 12 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 36 222 2 4 18 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 222 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7
  36 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 222 6 1 6 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 222
  (Polychromatic418967fa.accept_15_5_6_12_1_916 5 36 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 36 222 2 2 18 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 36 222 3 1 12 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 36 222 2 1 18 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 222 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 36 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 222)))))))))))))))))))))))))))))))))))) (allB_succ 35 222
  (allA_succ_of_accept 34 35 222 (accept_3_4 34 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  35 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 35 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 222 (accept_3_4 31 35 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 35 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 222 (accept_3_4 28 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 222 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 222 (Polychromatic418967fa.accept_21_5_14_12_1_8720 26 35 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 222 (accept_3_4 25 35 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 222 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 35
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 222
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 222 (accept_3_4 22 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 35 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 222 (accept_3_4 19 35 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 222 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 35 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 222 (accept_3_4 16 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 222 (Polychromatic418967fa.accept_13_2_9_1_1_67 15 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 35 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 222 (accept_3_4 13 35 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 35 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 222
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 222 (accept_3_4 10 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 222 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 35 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 222 (accept_3_4 7 35 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 222 (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 35 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 222 (accept_3_4 4 35 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 35
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 222
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 222 (accept_3_4 1 35 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  222))))))))))))))))))))))))))))))))))) (allB_succ 34 222 (allA_succ_of_accept 33 34 222
  (Polychromatic418967fa.accept_12_9_10_6_1_872 33 34 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 222 2 16 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 34 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 34 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 222 2 15 17 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 222 (accept_3_5 29 34 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 222 2 14 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 222 (Polychromatic418967fa.accept_10_7_4_2_1_903 27
  34 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 222 2 13 17 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 34 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 222 2 12 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 34 222 (accept_3_5 23 34 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 34 222 2 11 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 34 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 34 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 34 222 2 10 17 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 34 222
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 34 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 34 222 2 9 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 34 222 (accept_3_5 17 34 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34
  222 2 8 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  34 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 34 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 34 222 2 7 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 34 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 34 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 222 2 6 17 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 222 (accept_3_5 11 34 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 222 2 5 17 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 222
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 34 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 222 2 4 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 222 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 34 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 222 2 3 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 222 (accept_3_5 5 34 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 222 2 2 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 34 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 222 2 1 17 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 34
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 222))))))))))))))))))))))))))))))))))
  (allB_succ 33 222 (allA_succ_of_accept 32 33 222 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 33 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 222 3 10 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 222 (Polychromatic418967fa.accept_13_3_7_1_1_334 29 33 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 222 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 33 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 222 3 9 11 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 222
  (Polychromatic418967fa.accept_12_2_9_6_1_439 26 33 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 222 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 33 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 222 3 8 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 222
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 33 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 222 3 7 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 222 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 33 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 222 3 6 11 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 222
  (Polychromatic418967fa.accept_14_3_5_12_1_4000 17 33 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 222 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 33 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 222 3 5 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 222 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 33 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 222
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 33 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 222 3 4 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 222 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 33
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 222 3 3 11 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 222
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 33 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 222 3 2 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 222 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 33 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 222
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 33 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 222 3 1 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 222 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 33 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 222 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 33 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 222)))))))))))))))))))))))))))))))))
  (allB_succ 32 222 (allA_succ_of_accept 31 32 222 (accept_3_4 31 32 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 32 222 2 15 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 32 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 32 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 32 222 2 14 16 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 32 222
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 32 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 32 222 2 13 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 32 222 (accept_3_4 25 32 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 32 222 2 12 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 32 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 32 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 222 2 11 16 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 222
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 222 2 10 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 32 222 (accept_3_4 19 32 222 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 32 222 2 9 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 32 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 32 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 222 2 8 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  32 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 222 2 7 16 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 222 (accept_3_4 13
  32 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 222 2 6 16 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 32 222
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 32 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 32 222 2 5 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 32 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 32 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 222 2 4 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 222 (accept_3_4 7 32 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 32 222 2 3 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 32 222 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 32 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 222 2 2 16 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 32
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 222 2 1 16 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 222 (accept_3_4 1 32
  222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 222)))))))))))))))))))))))))))))))) (allB_succ 31 222
  (allA_succ_of_accept 30 31 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 31 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 222 (accept_3_5 29 31 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 31 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 222
  (Polychromatic418967fa.accept_17_10_14_1_1_5823 27 31 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 222 (accept_3_5 26 31 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  31 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 222 (Polychromatic418967fa.accept_19_5_12_13_1_9115 24 31 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 222 (accept_3_5 23 31 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 31 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 222 (accept_3_5 20 31 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  31 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 31 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 222 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 31 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 222 (accept_3_5 17 31 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 31 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 222
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 31 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 222 (accept_3_5 14 31 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 31 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 222 (accept_3_5 11 31 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 31 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 222 (accept_3_5 8 31 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  222 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 222 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 31 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 222 (accept_3_5 5 31 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 222 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 31 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 222 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  31 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 222 (accept_3_5 2 31 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 222)))))))))))))))))))))))))))))))
  (allB_succ 30 222 (allA_succ_of_accept 29 30 222 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 30 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 222 2 14 15 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 222 3 9 10 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 222 2 13 15 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 30 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 30 222 6 4 5 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 30 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 222 2 11 15 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 30 222 3 7 10 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 222 2 10 15 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 222
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 30 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 222 6 3 5 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 30 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 222 2 8 15 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 222 3 5 10 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 222 2 7 15 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 13
  30 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 222 6 2 5 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 30 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 222 2 5 15 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 30 222 3 3 10 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 30 222 2 4 15 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 30 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 222 6 1 5 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 30 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 222 2 2 15 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 30 222 3 1 10 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 30 222 2 1 15 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 222
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 30 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 222)))))))))))))))))))))))))))))) (allB_succ 29 222 (allA_succ_of_accept 28 29 222 (accept_3_4 28 29 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  29 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 222
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 29 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 222 (accept_3_4 25 29 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 29 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 222 (accept_3_4 22 29 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 29 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 222 (accept_3_4 19 29 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 29 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 29 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 222 (accept_3_4 16 29 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 222
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 29 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 222 (accept_3_4 13 29 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 29 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 222 (accept_3_4 10 29 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 222 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 29 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 222
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 29 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 222 (accept_3_4 7 29 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  222 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 29 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 222 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 29 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 222 (accept_3_4 4 29 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 222 (Polychromatic418967fa.accept_13_2_3_1_1_3823 2
  29 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 222 (accept_3_4 1 29 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 222))))))))))))))))))))))))))))) (allB_succ 28 222
  (allA_succ_of_accept 27 28 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 28 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 222 2 13 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 25
  28 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 222 2 12 14 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 222 (accept_3_5 23
  28 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 222 2 11 14 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 222
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 28 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 28 222 2 10 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 28 222 (Polychromatic418967fa.accept_13_6_2_1_1_2137 19 28 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 222 2 9 14 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 222 (accept_3_5 17 28 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 222 2 8 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 28 222 (Polychromatic418967fa.accept_10_5_8_2_1_517 15
  28 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 222 2 7 14 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 222
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 28 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 28 222 2 6 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 28 222 (accept_3_5 11 28 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28
  222 2 5 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  28 222 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 28 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 28 222 2 4 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 28 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 28 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 222 2 3 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 222 (accept_3_5 5 28 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 222 2 2 14 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 28 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 222 2 1 14 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 222
  (Polychromatic418967fa.accept_15_1_13_12_1_347 1 28 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 222)))))))))))))))))))))))))))) (allB_succ 27 222 (allA_succ_of_accept 26 27 222
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 27 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 222 3 8 9 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 222 (Polychromatic418967fa.accept_19_4_8_13_1_7802 23 27 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 22 27 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 222 3 7 9 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 222 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 27 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 222 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 27 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 222 3 6 9 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 222 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 27 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 222 3 5 9 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 222 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 27 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 222 3 4 9 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 27 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 222 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 27 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 222 3 3 9 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 222
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 27 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 222 (Polychromatic418967fa.accept_17_7_10_1_1_4488 7 27 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 222 3 2 9 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 222
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 27 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 222 3 1 9 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 222 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 27 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 222))))))))))))))))))))))))))) (allB_succ 26
  222 (allA_succ_of_accept 25 26 222 (accept_3_4 25 26 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24
  26 222 2 12 13 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 26 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 26 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 26 222 2 11 13 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 26 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 21
  26 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 222 2 10 13 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 222 (accept_3_4 19
  26 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 222 2 9 13 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 222
  (Polychromatic418967fa.accept_11_6_4_2_1_599 17 26 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 26 222 2 8 13 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 26 222 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 26 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 222 2 7 13 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 222 (accept_3_4 13 26 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 222 2 6 13 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 222 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 26 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 222 2 5 13 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 222
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 26 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 26 222 2 4 13 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 26 222 (accept_3_4 7 26 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 222
  2 3 13 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26
  222 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 26 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 26 222 2 2 13 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 26 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 26 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 222 2 1 13 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 222 (accept_3_4 1 26 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 222)))))))))))))))))))))))))) (allB_succ 25 222 (allA_succ_of_accept 24 25 222
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 25 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 222 (accept_3_5 23 25 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 25 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 25 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 222 (accept_3_5 20 25 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 222
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 25 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 222 (accept_3_5 17 25 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 25 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 222 (accept_3_5 14 25 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 222
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 25 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 222 (accept_3_5 11 25 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 222 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 25 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 25 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 222 (accept_3_5 8 25 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 222
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 25 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 222 (accept_3_5 5 25 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  222 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 25 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 222 (accept_3_5 2 25 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 222))))))))))))))))))))))))) (allB_succ 24 222
  (allA_succ_of_accept 23 24 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 222 2 11 12 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 222 3 7 8 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 222 2 10 12 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 222
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 19 24 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 24 222 6 3 4 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 24 222 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 24 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 222 2 8 12 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 24 222 3 5 8 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 24 222 2 7 12 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 222
  (Polychromatic418967fa.accept_21_13_3_12_1_10213 13 24 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 24 222 6 2 4 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 24 222 (Polychromatic418967fa.accept_17_11_7_1_1_7023 11 24 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 222 2 5 12 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 222 3 3 8 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 222 2 4 12 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 222
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 24 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 222 6 1 4 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 222 (Polychromatic418967fa.accept_14_5_10_12_1_1454 5 24 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 222 2 2 12 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 222 3 1 8 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 222 2 1 12 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 222)))))))))))))))))))))))) (allB_succ 23
  222 (allA_succ_of_accept 22 23 222 (accept_3_4 22 23 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 23 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 23 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 222 (accept_3_4 19 23 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 23 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 222 (accept_3_4 16 23 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 222 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 23 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 222 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 23 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 222 (accept_3_4 13 23 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 23 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 222
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 23 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 222 (accept_3_4 10 23 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 222 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 23 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 222 (accept_3_4 7 23 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 222 (Polychromatic418967fa.accept_19_6_4_13_1_2329 6 23 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 222 (accept_3_4 4 23 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  23 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 222
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 23 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 222 (accept_3_4 1 23 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  222))))))))))))))))))))))) (allB_succ 22 222 (allA_succ_of_accept 21 22 222
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 22 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 222 2 10 11 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 22 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 22 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 222 2 9 11 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 222 (accept_3_5 17 22 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22 222 2 8 11 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 22 222 (Polychromatic418967fa.accept_12_3_10_6_1_442
  15 22 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 222 2 7 11 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 222
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 22 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 22 222 2 6 11 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 22 222 (accept_3_5 11 22 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22
  222 2 5 11 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  22 222 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 22 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 22 222 2 4 11 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 22 222 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 22 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 222 2 3 11 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 222 (accept_3_5 5 22 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 222 2 2 11 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 22 222 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 22 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 222 2 1 11 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 222
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 22 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 222)))))))))))))))))))))) (allB_succ 21 222 (allA_succ_of_accept 20 21 222
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 222 3 6 7 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 222 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 222
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 21 222 3 5 7 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 21 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 21 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 222 3 4 7 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 21 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 222 3 3 7 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 222 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 21 222 3 2 7 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 21 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 222 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 222 3 1 7 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 222
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 21 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 222 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 21 222))))))))))))))))))))) (allB_succ 20 222 (allA_succ_of_accept 19 20 222
  (accept_3_4 19 20 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 222 2 9 10 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 222
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 20 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 222 2 8 10 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 20 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 222 2 7 10 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 222 (accept_3_4 13 20 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 222 2 6 10 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 20 222 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 20 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 222 2 5 10 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 222
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 20 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 222 2 4 10 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 222 (accept_3_4 7 20 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 222
  2 3 10 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  222 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 20 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 222 2 2 10 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 20 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 222 2 1 10 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 222 (accept_3_4 1 20 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 222)))))))))))))))))))) (allB_succ 19 222 (allA_succ_of_accept 18 19 222
  (Polychromatic418967fa.accept_13_5_6_1_1_822 18 19 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 222 (accept_3_5 17 19 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 19 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 222 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 19 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 222 (accept_3_5 14 19 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 222
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 19 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 222 (accept_3_5 11 19 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 222 (Polychromatic418967fa.accept_14_10_5_12_1_3995 10 19 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 222 (accept_3_5 8 19 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 222
  (Polychromatic418967fa.accept_17_6_2_1_1_3350 6 19 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 222 (accept_3_5 5 19 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  222 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 19 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 19 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 222 (accept_3_5 2 19 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 222))))))))))))))))))) (allB_succ 18 222 (allA_succ_of_accept 17
  18 222 (Polychromatic418967fa.accept_13_4_5_1_1_833 17 18 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 18 222 2 8 9 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 18 222 3 5 6 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 18 222 2 7 9 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 222 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 18 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 222 6 2 3 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 222
  (Polychromatic418967fa.accept_21_11_18_12_1_1494 11 18 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 222 2 5 9 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 18 222 3 3 6 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 18 222 2 4 9 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 18 222 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 18 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 222 6 1 3 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 222 (Polychromatic418967fa.accept_10_5_8_2_1_517 5
  18 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 222 2 2 9 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 222 3 1 6 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 222 2 1 9 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 18 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 222)))))))))))))))))) (allB_succ 17 222 (allA_succ_of_accept 16 17 222 (accept_3_4 16 17 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 222
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 17 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 222 (accept_3_4 13 17 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 222 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 17 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 222 (accept_3_4 10 17 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 222 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 17 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 222
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 17 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 222 (accept_3_4 7 17 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  222 (Polychromatic418967fa.accept_15_6_2_12_1_885 6 17 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 17 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 222 (accept_3_4 4 17 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 17 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 222 (accept_3_4 1 17 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  222))))))))))))))))) (allB_succ 16 222 (allA_succ_of_accept 15 16 222 (Polychromatic418967fa.accept_12_3_4_6_1_434 15
  16 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 16 222 2 7 8 111 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 16 222
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 16 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 16 222 2 6 8 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 16 222 (accept_3_5 11 16 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 16
  222 2 5 8 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  16 222 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 16 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 16 222 2 4 8 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 16 222 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 16 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 222 2 3 8 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 222 (accept_3_5 5 16 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 222 2 2 8 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 16 222 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 16 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 222 2 1 8 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 222
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 16 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 222)))))))))))))))) (allB_succ 15 222 (allA_succ_of_accept 14 15 222
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 15 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 222 3 4 5 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 15 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 10 15 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 222 3 3 5 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 222 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 15 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 222 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 15 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 222 3 2 5 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 222 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 15 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 222 3 1 5 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 222 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 15 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 222
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 222))))))))))))))) (allB_succ 14 222 (allA_succ_of_accept 13 14 222 (accept_3_4 13 14 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 222 2 6 7 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 14 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 222 2 5 7 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 222
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 14 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 222 2 4 7 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 14 222 (accept_3_4 7 14 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 222
  2 3 7 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14
  222 (Polychromatic418967fa.accept_19_5_14_13_1_7816 5 14 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 14 222 2 2 7 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 14 222 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 14 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 222 2 1 7 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 222 (accept_3_4 1 14 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 14 222)))))))))))))) (allB_succ 13 222 (allA_succ_of_accept 12 13 222
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 13 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 222 (accept_3_5 11 13 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 222 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 13 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 222 (Polychromatic418967fa.accept_18_9_13_6_1_877 9 13 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 222 (accept_3_5 8 13 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 222
  (Polychromatic418967fa.accept_14_6_13_12_1_810 6 13 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 222 (accept_3_5 5 13 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  222 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 13 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 222 (accept_3_5 2 13 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 222))))))))))))) (allB_succ 12 222 (allA_succ_of_accept 11 12
  222 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 12 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 222 2 5 6 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 12 222 3 3 4 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 12 222 2 4 6 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 222 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 222 6 1 2 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 222 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 222 2 2 6 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 12 222 3 1 4 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 12 222 2 1 6 111 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 222
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 12 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 222)))))))))))) (allB_succ 11 222 (allA_succ_of_accept 10 11 222 (accept_3_4 10 11 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 222
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 11 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 222 (accept_3_4 7 11 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  222 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 11 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 222 (accept_3_4 4 11 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 222 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 11 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 222 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  11 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 222 (accept_3_4 1 11 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 222))))))))))) (allB_succ 10 222 (allA_succ_of_accept 9 10 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 10 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 222 2 4 5 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 222 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 10 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 222 2 3 5 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 222 (accept_3_5 5 10 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 222 2 2 5 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 222 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 10 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 222 2 1 5 111 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 222 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 10
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 222)))))))))) (allB_succ 9 222
  (allA_succ_of_accept 8 9 222 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 9 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 222 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 222 3 2 3 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 222
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 9 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 222 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 9 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 222 3 1 3 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 222 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 9 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 222
  (Polychromatic418967fa.accept_10_1_9_2_1_45 1 9 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 222))))))))) (allB_succ 8 222 (allA_succ_of_accept 7 8 222 (accept_3_4 7 8 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 222 2 3 4 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 8 222 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 8 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 222 2 2 4 111 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 222
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 8 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 8 222 2 1 4 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 8 222 (accept_3_4 1 8 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 222))))))))
  (allB_succ 7 222 (allA_succ_of_accept 6 7 222 (Polychromatic418967fa.accept_13_6_7_1_1_335 6 7 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 222 (accept_3_5 5 7 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 7 222 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 7 222 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 222 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 222 (accept_3_5 2 7 222
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7
  222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 222))))))) (allB_succ 6 222
  (allA_succ_of_accept 5 6 222 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 6 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 222 2 2 3 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 6 222 3 1 2 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 6 222 2 1 3 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 222 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 6 222
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 222)))))) (allB_succ 5 222
  (allA_succ_of_accept 4 5 222 (accept_3_4 4 5 222 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 222
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 222 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 5 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 222 (accept_3_4 1 5 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 222))))) (allB_succ 4 222 (allA_succ_of_accept 3 4 222
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 4 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 4 222 2 1 2 111 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 4 222 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 4 222 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 4 222)))) (allB_succ 3 222 (allA_succ_of_accept 2 3 222
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 3 222 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 222 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 222 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 3 222))) (allB_succ 2 222 (allA_succ_of_accept 1 2 222 (accept_3_4 1 2 222 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 2 222)) (allB_two
  222)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


