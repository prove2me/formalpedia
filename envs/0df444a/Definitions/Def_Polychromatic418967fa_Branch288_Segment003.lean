-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch288_Segment003
-- name    : Polychromatic418967fa_Branch288_Segment003
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:06:29.680099+00:00
-- url     : https://prove2.me/theorems/68974284-57d1-4357-a692-c0ccaacd8a85
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch288_Segment002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_288_segment_003 : allB 241 288 :=
  allB_succ' 49 240 288 (Eq.refl Bool.true) (allA_succ_of_gcd 48 240 288 48 1 5 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 240 288
  (Polychromatic418967fa.accept_13_8_6_2_1_865 47 240 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 240 288 2 23 120 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 240 288 3 15 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 240 288 4 11 60 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 240 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437 43 240
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 240 288 6 7 40 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 240 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 240 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 240 288 8 5 30 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 240 288 3 13 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 240 288 2 19 120 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 240 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 37 240 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 240 288 12 3 20 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 240 288
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 240 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 240 288 2 17 120 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 240 288 3 11 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 240 288 16 2 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 240 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 240 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 240 288 6 5 40 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 240 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 29 240 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 240 288 4 7 60 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 240 288 3 9 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 240 288 2 13 120 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 240 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 25 240 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 240 288 24 1 10 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 240 288
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 240 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 240 288 2 11 120 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 240 288 3 7 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 240 288 4 5 60 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 240 288 (Polychromatic418967fa.accept_21_19_9_15_1_4217 19 240 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 240 288 6 3 40 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 240 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 240 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 240 288 16 1 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 240 288 3 5 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 240 288 2 7 120 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 240 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 240 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 240 288 12 1 20 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 240 288
  (Polychromatic418967fa.accept_19_11_12_3_1_8407 11 240 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 240 288 2 5 120 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 240 288 3 3 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 240 288 8 1 30 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 240 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 240 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 240 288 6 1 40 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 240 288
  (Polychromatic418967fa.accept_17_5_2_16_1_1294 5 240 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 240 288 4 1 60 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 240 288 3 1 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 240 288 2 1 120 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 240 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 1 240 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240 288)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 239 288 (Eq.refl Bool.true) (allA_succ_of_accept 49 239 288 (accept_3_4 49 239 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 239 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 48 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 239 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 239 288 (accept_3_4 46 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 239 288 (Polychromatic418967fa.accept_21_3_8_15_1_4301 45 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 239 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 239 288 (accept_3_4 43 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 239 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 42 239
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 239 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 41 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 239 288 (accept_3_4 40 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 239 288 (Polychromatic418967fa.accept_17_5_1_16_1_4359 39 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 239 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 38 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 239 288 (accept_3_4 37 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 239 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 239
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 239 288
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 239 288 (accept_3_4 34 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 239 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 33 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 239 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 32 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 239 288 (accept_3_4 31 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 239 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 239
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 239 288
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 239 288 (accept_3_4 28 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 239 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 239 288 (Polychromatic418967fa.accept_15_11_14_3_1_1965 26 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 239 288 (accept_3_4 25 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 239 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 239
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 239 288
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 239 288 (accept_3_4 22 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 239 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 239 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 20 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 239 288 (accept_3_4 19 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 239 288 (Polychromatic418967fa.accept_19_18_11_3_1_11183 18
  239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 239 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 239 288 (accept_3_4 16 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 239 288 (Polychromatic418967fa.accept_17_15_1_16_1_8166 15 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 239 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 239 288 (accept_3_4 13 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 239 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 239
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 239 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 11 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 239 288 (accept_3_4 10 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  239 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 239 288 (Polychromatic418967fa.accept_19_8_11_3_1_5539 8 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 288 (accept_3_4 7 239 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 239 288 (Polychromatic418967fa.accept_21_6_8_15_1_8903 6 239
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 5 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 239 288 (accept_3_4 4 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  239 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 239 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 239 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 2 239 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 288 (accept_3_4 1 239 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 239 288)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 238 288
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 238 288 2 25 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 238 288 (Polychromatic418967fa.accept_19_11_10_3_1_2934 49 238
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 238 288 2 24 119 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 238 288 (accept_3_5 47
  238 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 238 288 2 23 119 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 238 288
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 238 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 238 288 2 22 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 238 288 (Polychromatic418967fa.accept_19_5_10_3_1_5460 43 238 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 238 288 2 21 119 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 238 288 (accept_3_5 41 238 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 238 288 2 20 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 238 288
  (Polychromatic418967fa.accept_15_9_13_3_1_535 39 238 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 238 288 2 19 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 238 288 (Polychromatic418967fa.accept_13_11_4_2_1_2954 37 238 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 238 288 2 18 119 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 238 288 (accept_3_5 35 238 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 238 288 2 17 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 238 288
  (Polychromatic418967fa.accept_20_13_18_8_1_4936 33 238 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 238 288 2 16 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 238 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 238 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 238 288 2 15 119 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 238 288 (accept_3_5 29 238 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 238 288 2 14 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 238 288
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 238 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 238 288 2 13 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 238 288 (Polychromatic418967fa.accept_13_12_4_2_1_2955 25 238 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 238 288 2 12 119 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 238 288 (accept_3_5 23 238 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 238 288 2 11 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 238 288
  (Polychromatic418967fa.accept_20_1_18_8_1_6359 21 238 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 238 288 2 10 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 238 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 19 238 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 238 288 2 9 119 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 238 288 (accept_3_5 17 238 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 238 288 2 8 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 238 288
  (Polychromatic418967fa.accept_19_15_10_3_1_12550 15 238 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 238 288 2 7 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 238 288 (Polychromatic418967fa.accept_19_13_10_3_1_11235 13 238 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 238 288 2 6 119 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 238 288 (accept_3_5 11
  238 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 238 288 2 5 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 238 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 238 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 238 288 2 4 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 238 288 (Polychromatic418967fa.accept_19_7_10_3_1_4149 7 238 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 238 288 2 3 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 238 288 (accept_3_5 5 238 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 238 288 2 2 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 238 288 (Polychromatic418967fa.accept_20_3_18_8_1_4859
  3 238 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 238 288 2 1 119 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 238 288
  (Polychromatic418967fa.accept_15_1_13_3_1_2002 1 238 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 238 288))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 237 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 237 288 3 17 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 237 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 50 237 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 237 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 237 288 3 16 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 237 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 237 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 237 288
  (Polychromatic418967fa.accept_21_4_6_15_1_5744 46 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 237 288 3 15 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 237 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 237 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 237 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 43 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 237 288 3 14 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 237 288 (Polychromatic418967fa.accept_21_20_6_15_1_11937 41 237 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 237 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 40 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 237 288 3 13 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 237 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 38 237 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 237 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 237 288 3 12 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 237 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 237 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 237 288
  (Polychromatic418967fa.accept_19_15_9_3_1_13764 34 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 237 288 3 11 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 237 288 (Polychromatic418967fa.accept_15_2_12_3_1_1183 32 237 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 237 288
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 31 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 237 288 3 10 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 237 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 237 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 237 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 28 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 237 288 3 9 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 237 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 237 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 237 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 237 288 3 8 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 237 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 237 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 22 237
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 237 288 3 7 79 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 237 288
  (Polychromatic418967fa.accept_21_20_6_15_1_11937 20 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 237 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 237 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 237 288 3 6 79 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 237 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 237 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 237 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 237 288 3 5 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 237 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429
  14 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 237 288 3 4 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 237 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 237 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 288
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 10 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 237 288 3 3 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 237 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 237 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 7 237
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 237 288 3 2 79 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 237 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 237 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 237 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 237 288 3 1 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 237 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 237 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 237 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 237 288)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 236 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 52 236 288 4 13 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 236 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 236 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 236 288 2 25 118 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 236 288 (accept_3_4 49 236 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 236 288 4 12 59 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 236 288
  (Polychromatic418967fa.accept_22_3_16_2_1_10045 47 236 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 236 288 2 23 118 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 236 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 236 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 236 288 4 11 59 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 236 288 (accept_3_4 43 236 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 236 288 2 21 118 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 236 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 236 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 236 288 4 10 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 236 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 236 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 236 288 2 19 118 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 236 288 (accept_3_4 37 236 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 236 288 4 9 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 236 288
  (Polychromatic418967fa.accept_17_1_15_16_1_2202 35 236 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 236 288 2 17 118 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 236 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 236 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 236 288 4 8 59 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 236 288 (accept_3_4 31 236 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 236 288 2 15 118 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 236 288
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 29 236 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 236 288 4 7 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 236 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 236 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 236 288 2 13 118 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 236 288 (accept_3_4 25 236 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 236 288 4 6 59 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 236 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 236 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 236 288 2 11 118 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 236 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 236 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 236 288 4 5 59 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 236 288 (accept_3_4 19 236 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 236 288 2 9 118 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 236 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 236 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 236 288 4 4 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 236 288 (Polychromatic418967fa.accept_19_15_8_3_1_13786 15 236 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 236 288 2 7 118 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 236 288 (accept_3_4 13 236 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 236 288 4 3 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 236 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 11
  236 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 236 288 2 5 118 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 236 288
  (Polychromatic418967fa.accept_21_9_5_15_1_5741 9 236 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 236 288 4 2 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 236 288 (accept_3_4 7 236 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 236
  288 2 3 118 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  236 288 (Polychromatic418967fa.accept_19_5_8_3_1_5498 5 236 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 236 288 4 1 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 236 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 236 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 236 288 2 1 118 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 236 288 (accept_3_4 1 236 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 236 288))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54
  235 288 (Eq.refl Bool.true) (allA_succ_of_accept 53 235 288 (accept_3_5 53 235 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 235 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 235 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 235 288 (Polychromatic418967fa.accept_13_12_1_2_1_845
  51 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 235 288 (accept_3_5 50
  235 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 235 288
  (Polychromatic418967fa.accept_17_15_14_16_1_5625 49 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 235 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 48 235 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 235 288 (accept_3_5 47 235 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 235 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 46 235
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 235 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 235 288 (accept_3_5 44 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 235 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 235 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 235 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 235 288 (accept_3_5 41 235 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 235 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 235 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 235 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 39 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 235 288 (accept_3_5 38 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 235 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 235 288 (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 235 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 235 288 (accept_3_5 35 235 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 235 288 (Polychromatic418967fa.accept_19_15_7_3_1_4143 34 235
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 235 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 235 288 (accept_3_5 32 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 235 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 235 288 (Polychromatic418967fa.accept_20_10_15_8_1_4818 30 235 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 235 288 (accept_3_5 29 235 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 235 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 235
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 235 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 235 288 (accept_3_5 26 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 235 288 (Polychromatic418967fa.accept_13_12_1_2_1_845 25 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 235 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 235 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 235 288 (accept_3_5 23 235 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 235 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 235 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 235 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 235 288 (accept_3_5 20 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 235 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 235 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 235 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 235 288 (accept_3_5 17 235 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 235 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 16 235
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 235 288
  (Polychromatic418967fa.accept_17_15_14_16_1_5625 15 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 235 288 (accept_3_5 14 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 235 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 235 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 235 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 235 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 235 288 (accept_3_5 11 235 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 235 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 10
  235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 235 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 235 288 (accept_3_5 8 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  235 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 235 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 235 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 235 288 (accept_3_5 5 235 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 235 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 235 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 235 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 235 288 (accept_3_5 2 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  235 288 (Polychromatic418967fa.accept_22_1_15_2_1_3668 1 235 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 235 288)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 234 288 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 234 288 18 3 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 234 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 234 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 234 288 2 26 117 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 234 288 3 17 78 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 234 288 2 25 117 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 234 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 234 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 234 288 6 8 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 234 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 234 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 234 288 2 23 117 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 234 288 9 5 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 234 288 2 22 117 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 234 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 43 234 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 234 288 6 7 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 234 288 (Polychromatic418967fa.accept_22_19_14_2_1_3635 41 234 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 234 288 2 20 117 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 234 288 3 13 78 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 234 288 2 19 117 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 234 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 234 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 234 288 18 2 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 234 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 35 234 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 234 288 2 17 117 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 234 288 3 11 78 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 234 288 2 16 117 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 234 288
  (Polychromatic418967fa.accept_21_10_3_15_1_13463 31 234 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 234 288 6 5 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 234 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 234 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 234 288 2 14 117 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 234 288 9 3 26 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 234 288 2 13 117 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 234 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 234 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 234 288 6 4 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 234 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 234 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 234 288 2 11 117 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 234 288 3 7 78 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 234 288 2 10 117 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 234 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 234 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 234 288 18 1 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 234 288 (Polychromatic418967fa.accept_19_17_6_3_1_9830 17 234 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 234 288 2 8 117 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 234 288 3 5 78 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 234 288 2 7 117 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 234 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 234 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 234 288 6 2 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 234 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 234 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 234 288 2 5 117 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 234 288 9 1 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 234 288 2 4 117 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 288
  (Polychromatic418967fa.accept_19_7_6_3_1_6998 7 234 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 288 6 1 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 234 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 234 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 234 288 2 2 117 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 234 288 3 1 78 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 234 288 2 1 117 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 234 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 288))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 233 288 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 233 288 (accept_3_4 55 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 233 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 54 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 233 288 (Polychromatic418967fa.accept_13_1_12_2_1_384 53 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 233 288 (accept_3_4 52 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 233 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 233
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 233 288
  (Polychromatic418967fa.accept_15_5_8_3_1_556 50 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 233 288 (accept_3_4 49 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 233 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 233 288 (Polychromatic418967fa.accept_17_13_12_16_1_6908 47 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 233 288 (accept_3_4 46 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 233 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 233 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 233 288
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 44 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 233 288 (accept_3_4 43 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 233 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 42 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 233 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 233 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 233 288 (accept_3_4 40 233 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 233 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 39 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 233 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 233 288 (accept_3_4 37 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 233 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 233 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 233 288 (accept_3_4 34 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 233 288 (Polychromatic418967fa.accept_19_14_5_3_1_859 33 233
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 233 288
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 32 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 233 288 (accept_3_4 31 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 233 288 (Polychromatic418967fa.accept_13_4_12_2_1_1459 30 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 233 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 29 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 233 288 (accept_3_4 28 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 233 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 233 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 233 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 233 288 (accept_3_4 25 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 233 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 233 288 (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 233 288 (accept_3_4 22 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 233 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 233
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 233 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 233 288 (accept_3_4 19 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 233 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 233 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 233 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 233 288 (accept_3_4 16 233 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 233 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 233 288
  (Polychromatic418967fa.accept_13_1_12_2_1_384 14 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 233 288 (accept_3_4 13 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 233 288 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 233 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 288 (accept_3_4 10 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 233 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 288
  (Polychromatic418967fa.accept_19_8_5_3_1_4181 8 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 233 288 (accept_3_4 7 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  233 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 233 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 233 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 288 (accept_3_4 4 233 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 233 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 288
  (Polychromatic418967fa.accept_19_2_5_3_1_5536 2 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 288 (accept_3_4 1 233 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 232 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 232 288 8 7 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 232 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 55 232 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 232 288 2 27 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 232 288 (accept_3_5 53 232 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 232 288 4 13 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 232 288 (Polychromatic418967fa.accept_19_13_4_3_1_2945 51 232
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 232 288 2 25 116 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 232 288
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 49 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 232 288 8 6 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 232 288 (accept_3_5 47 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 232 288 2 23 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 232 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 232 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 232 288 4 11 58 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 232 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 232 288 2 21 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 232 288 (accept_3_5 41 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 232 288 8 5 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 232 288 (Polychromatic418967fa.accept_17_5_11_16_1_3257 39 232 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 232 288 2 19 116 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 232 288
  (Polychromatic418967fa.accept_19_18_4_3_1_4140 37 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 232 288 4 9 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 232 288 (accept_3_5 35 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  232 288 2 17 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 232 288 (Polychromatic418967fa.accept_21_12_1_15_1_8924 33 232 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 232 288 8 4 29 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 232 288
  (Polychromatic418967fa.accept_17_14_11_16_1_3261 31 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 232 288 2 15 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 232 288 (accept_3_5 29 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 232 288 4 7 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 232 288 (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 232 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 232 288 2 13 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 232 288 (Polychromatic418967fa.accept_10_5_2_8_1_135
  25 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 232 288 8 3 29 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 232 288
  (accept_3_5 23 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 232 288 2 11 116 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 232 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 232 288 4 5 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 232 288 (Polychromatic418967fa.accept_15_4_7_3_1_119 19 232 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 232 288 2 9 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 232 288 (accept_3_5 17 232 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 232 288 8 2 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 232 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 232 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 232 288 2 7 116 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 232 288
  (Polychromatic418967fa.accept_19_13_4_3_1_2945 13 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 232 288 4 3 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 232 288 (accept_3_5 11 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  232 288 2 5 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 232 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 232 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 232 288 8 1 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 232 288 (Polychromatic418967fa.accept_19_7_4_3_1_5533 7 232 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 232 288 2 3 116 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 232 288 (accept_3_5 5
  232 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 232 288 4 1 58 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 232 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 232 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 232 288 2 1 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 232 288 (Polychromatic418967fa.accept_19_1_4_3_1_8404 1 232 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 232 288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 58 231 288 (Eq.refl Bool.true) (allA_succ_of_gcd 57 231 288 3 19 77 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 231 288
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 56 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 231 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 55 231 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 231 288 3 18 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 231 288 (Polychromatic418967fa.accept_10_3_1_8_1_132
  53 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 231 288
  (Polychromatic418967fa.accept_22_8_11_2_1_3507 52 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 231 288 3 17 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 231 288 (Polychromatic418967fa.accept_13_11_10_2_1_3840 50 231 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 231 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 49 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 231 288 3 16 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 231 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 47 231 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 231 288
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 46 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 231 288 3 15 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 231 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 44 231 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 231 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 43 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 231 288 3 14 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 231 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 41 231 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 231 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 40 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 231 288 3 13 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 231 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 38 231 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 231 288
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 37 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 231 288 3 12 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 231 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 231 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 231 288
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 34 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 231 288 3 11 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 231 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 32 231 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 231 288
  (Polychromatic418967fa.accept_13_5_10_2_1_856 31 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 231 288 3 10 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 231 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 231 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 288
  (Polychromatic418967fa.accept_22_6_11_2_1_11698 28 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 231 288 3 9 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 231 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 231 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 231 288
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 25 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 231 288 3 8 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 231 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 231 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 288
  (Polychromatic418967fa.accept_25_22_6_13_1_14248 22 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 231 288 3 7 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 231 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 20 231 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 231 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 19 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 231 288 3 6 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 231 288 (Polychromatic418967fa.accept_20_17_11_8_1_4894 17 231 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 288 (Polychromatic418967fa.accept_13_3_10_2_1_381
  16 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 231 288 3 5 77 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 231 288
  (Polychromatic418967fa.accept_22_14_11_2_1_8495 14 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 231 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 231 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 231 288 3 4 77 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 231 288
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 231 288 (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 231 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 231 288 3 3 77 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 231 288
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 8 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 288 (Polychromatic418967fa.accept_17_7_10_16_1_5582 7 231 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 231 288 3 2 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 231 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 5 231 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 288
  (Polychromatic418967fa.accept_23_4_1_12_1_17847 4 231 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 231 288 3 1 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 231 288 (Polychromatic418967fa.accept_25_2_6_13_1_17846 2 231 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 1 231 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 230 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 230 288 2 29 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 230 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 57 230 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 230 288 2 28 115 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 230 288 (accept_3_4 55 230 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 230 288 2 27 115 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 230 288
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 53 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 230 288 2 26 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 230 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 230 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 230 288 2 25 115 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 230 288 (accept_3_4 49 230 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 230 288 2 24 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 230 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47
  230 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 230 288 2 23 115 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 230 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 45 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 230 288 2 22 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 230 288 (accept_3_4 43 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 230 288 2 21 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 230 288 (Polychromatic418967fa.accept_25_16_5_13_1_17845 41 230 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 230 288 2 20 115 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 230 288
  (Polychromatic418967fa.accept_15_9_5_3_1_554 39 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 230 288 2 19 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 230 288 (accept_3_4 37 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 230 288 2 18 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 230 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 230 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 230 288 2 17 115 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 230 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 230 288 2 16 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 230 288 (accept_3_4 31 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 230 288 2 15 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 230 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 230 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 230 288 2 14 115 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 230 288
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 230 288 2 13 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 230 288 (accept_3_4 25 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 230 288 2 12 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 230 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 230 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 230 288 2 11 115 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 230 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 230 288 2 10 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 230 288 (accept_3_4 19 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 230 288 2 9 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 230 288 (Polychromatic418967fa.accept_15_2_5_3_1_552 17 230 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 230 288 2 8 115 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 230 288
  (Polychromatic418967fa.accept_20_15_10_8_1_6398 15 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 230 288 2 7 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 230 288 (accept_3_4 13 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 230 288 2 6 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 230 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 230 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 230 288 2 5 115 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 230 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 230 288 2 4 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 230 288 (accept_3_4 7 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 230 288 2 3 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 230 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 230 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 230 288 2 2 115 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 230 288
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 230 288 2 1 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 230 288 (accept_3_4 1 230 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 229 288 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 229 288 (accept_3_5 59 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 229 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 58 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 229 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 229 288 (accept_3_5 56 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 229 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 229 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 229 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 54 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 229 288 (accept_3_5 53 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 229 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 229 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 229 288 (accept_3_5 50 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 229 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 49 229
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 229 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 229 288 (accept_3_5 47 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 229 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 229 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 229 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 229 288 (accept_3_5 44 229 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 229 288 (Polychromatic418967fa.accept_17_9_8_16_1_2176 43 229 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 229 288
  (Polychromatic418967fa.accept_19_4_1_3_1_15091 42 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 229 288 (accept_3_5 41 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 229 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 229 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 229 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 229 288 (accept_3_5 38 229 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 229 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 229 288
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 229 288 (accept_3_5 35 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 229 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 229 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 229 288 (accept_3_5 32 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 229 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 229 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 229 288
  (Polychromatic418967fa.accept_19_11_1_3_1_5555 30 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 229 288 (accept_3_5 29 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 229 288 (Polychromatic418967fa.accept_21_7_19_15_1_4201 28 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 229 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 229 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 229 288 (accept_3_5 26 229 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 229 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 229 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 229 288 (accept_3_5 23 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 229 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 22 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 229 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 229 288 (accept_3_5 20 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 229 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 229
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 229 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 229 288 (accept_3_5 17 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 229 288 (Polychromatic418967fa.accept_15_1_4_3_1_1928 16 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 229 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 229 288 (accept_3_5 14 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 229 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 229 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 229 288
  (Polychromatic418967fa.accept_21_12_19_15_1_8942 12 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 229 288 (accept_3_5 11 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 229 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 229 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 288 (Polychromatic418967fa.accept_17_9_8_16_1_2176 9 229
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 288 (accept_3_5 8 229 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135
  7 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 229 288 (accept_3_5 5 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  229 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 229 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 229 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 229 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 288 (accept_3_5 2 229 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 229 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 228 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 228 288 12 5 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 228 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 228 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 228 288 2 29 114 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 228 288 3 19 76 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 228 288 4 14 57 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 228 288
  (Polychromatic418967fa.accept_21_13_18_15_1_2837 55 228 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 228 288 6 9 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 228 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 228 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 228 288 4 13 57 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 228 288 3 17 76 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 228 288 2 25 114 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 228 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 49 228 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 228 288 12 4 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 228 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 228 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 228 288 2 23 114 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 228 288 3 15 76 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 228 288 4 11 57 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 228 288
  (Polychromatic418967fa.accept_21_1_18_15_1_11934 43 228 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 228 288 6 7 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 228 288 (Polychromatic418967fa.accept_21_20_18_15_1_11881 41 228 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 228 288 4 10 57 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 228 288 3 13 76 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 228 288 2 19 114
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 228 288
  (Polychromatic418967fa.accept_17_3_7_16_1_3251 37 228 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 228 288 12 3 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 228 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 228 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 228 288 2 17 114 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 228 288 3 11 76 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 228 288 4 8 57 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 228 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 228 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 228 288 6 5 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 228 288 (Polychromatic418967fa.accept_21_8_18_15_1_5812 29 228 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 228 288 4 7 57 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 228 288 3 9 76 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 228 288 2 13 114 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 228 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 25 228 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 228 288 12 2 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 228 288 (Polychromatic418967fa.accept_17_6_7_16_1_6836 23 228 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 228 288 2 11 114 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 228 288 3 7 76 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 228 288 4 5 57 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 228 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 228 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 228 288 6 3 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 228 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 228 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 228 288 4 4 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 228 288 3 5 76 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 228 288 2 7 114 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 288
  (Polychromatic418967fa.accept_21_13_18_15_1_2837 13 228 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 228 288 12 1 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 228 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 228 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 228 288 2 5 114 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 228 288 3 3 76 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 228 288 4 2 57 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 288
  (Polychromatic418967fa.accept_21_7_18_15_1_2887 7 228 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 228 288 6 1 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 228 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 228 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 288 4 1 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 228 288 3 1 76 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 228 288 2 1 114 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 288
  (Polychromatic418967fa.accept_21_1_18_15_1_11934 1 228 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 228 288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 227 288
  (Eq.refl Bool.true) (allA_succ_of_accept 61 227 288 (accept_3_4 61 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 227 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 227 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 227 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 59 227
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 227 288 (accept_3_4 58 227
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 227 288
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 57 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 227 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437 56 227 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 227 288 (accept_3_4 55 227 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 227 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 227 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 227 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 227 288 (accept_3_4 52
  227 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 227 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 227 288 (Polychromatic418967fa.accept_15_5_2_3_1_4876 50 227 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 227 288 (accept_3_4 49 227 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 227 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 48 227 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 227 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 227 288 (accept_3_4 46 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 227 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 227 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 227 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 227 288 (accept_3_4 43 227 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 227 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 227 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 227 288
  (Polychromatic418967fa.accept_17_7_6_16_1_2195 41 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 227 288 (accept_3_4 40 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 227 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 227 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 38 227 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 227 288 (accept_3_4 37 227 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 227 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 227
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 227 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 227 288 (accept_3_4 34 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 227 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 227 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 227 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 227 288 (accept_3_4 31 227 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 227 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 227 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 227 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 227 288 (accept_3_4 28 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 227 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 227 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 227 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 227 288 (accept_3_4 25 227 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 227 288 (Polychromatic418967fa.accept_17_7_6_16_1_2195 24 227 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 227 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 227 288 (accept_3_4 22 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 227 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 227 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 227 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 288 (accept_3_4 19 227 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 227 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 227 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 288
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 227 288 (accept_3_4 16 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 227 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 227 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 14 227 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 288 (accept_3_4 13 227 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 227 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 288 (accept_3_4 10 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 227 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 288 (accept_3_4 7 227 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 288 (Polychromatic418967fa.accept_19_6_18_3_1_11230 6 227 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 288 (accept_3_4 4 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 288 (Polychromatic418967fa.accept_21_3_17_15_1_4199 3 227 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 227 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 288 (accept_3_4 1 227 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  226 288 (Eq.refl Bool.true) (allA_succ_of_gcd 62 226 288 2 31 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 226 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 61 226
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 226 288 2 30 113 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 226 288 (accept_3_5 59
  226 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 226 288 2 29 113 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 226 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 57 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 226 288 2 28 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 226 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 226 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 226 288 2 27 113 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 226 288 (accept_3_5 53 226 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 226 288 2 26 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 226 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173
  51 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 226 288 2 25 113 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 226 288
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 49 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 226 288 2 24 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 226 288 (accept_3_5 47 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 226 288 2 23 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 226 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 226 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 226 288 2 22 113 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 226 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 226 288 2 21 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 226 288 (accept_3_5 41 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 226 288 2 20 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 226 288 (Polychromatic418967fa.accept_19_1_17_3_1_1821 39 226 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 226 288 2 19 113 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 226 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 37 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 226 288 2 18 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 226 288 (accept_3_5 35 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 226 288 2 17 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 226 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 226 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 226 288 2 16 113 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 226 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 226 288 2 15 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 226 288 (accept_3_5 29 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 226 288 2 14 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 226 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 226 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 226 288 2 13 113 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 226 288
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 25 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 226 288 2 12 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 226 288 (accept_3_5 23 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 226 288 2 11 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 226 288 (Polychromatic418967fa.accept_15_6_1_3_1_2852 21 226 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 226 288 2 10 113 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 226 288
  (Polychromatic418967fa.accept_15_4_1_3_1_1922 19 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 226 288 2 9 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 226 288 (accept_3_5 17 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 226 288 2 8 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 226 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 226 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 226 288 2 7 113 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 226 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 226 288 2 6 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 226 288 (accept_3_5 11 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 226 288 2 5 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 226 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 226 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 226 288 2 4 113 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 226 288
  (Polychromatic418967fa.accept_13_7_5_2_1_401 7 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 226 288 2 3 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 226 288 (accept_3_5 5 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 226 288 2 2 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 226 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 226 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 288 2 1 113 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 1 226 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 225 288 (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 225 288 9 7 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 225 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 225 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 225 288
  (Polychromatic418967fa.accept_19_4_16_3_1_4175 61 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 225 288 3 20 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 225 288 (Polychromatic418967fa.accept_19_2_16_3_1_7005 59 225 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 225 288
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 58 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 225 288 3 19 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 225 288 (Polychromatic418967fa.accept_17_5_4_16_1_6925 56 225 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 225 288
  (Polychromatic418967fa.accept_19_17_16_3_1_8401 55 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 225 288 9 6 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 225 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 225 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 225 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 52 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 225 288 3 17 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 225 288 (Polychromatic418967fa.accept_13_11_4_2_1_2954 50 225 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 225 288
  (Polychromatic418967fa.accept_14_7_1_8_1_2873 49 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 225 288 3 16 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 225 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 225 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 225 288
  (Polychromatic418967fa.accept_27_19_9_18_1_17744 46 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 225 288 9 5 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 225 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 44 225 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 225 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 225 288 3 14 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 225 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 225 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 225 288
  (Polychromatic418967fa.accept_19_2_16_3_1_7005 40 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 225 288 3 13 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 225 288 (Polychromatic418967fa.accept_13_12_4_2_1_2955 38 225 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 225 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 225 288 9 4 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 225 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873 35 225 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 225 288 (Polychromatic418967fa.accept_19_15_16_3_1_8409 34 225
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 225 288 3 11 75 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 225 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 225 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 31 225 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 225 288 3 10 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 225 288 (Polychromatic418967fa.accept_22_7_5_2_1_17844
  29 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 288
  (Polychromatic418967fa.accept_23_5_18_12_1_17843 28 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 225 288 9 3 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 225 288 (Polychromatic418967fa.accept_22_4_5_2_1_14739 26 225 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 225 288
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 25 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 225 288 3 8 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 225 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 225 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 225
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 225 288 3 7 75 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 225 288
  (Polychromatic418967fa.accept_17_3_4_16_1_3208 20 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 225 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 225 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 225 288 9 2 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 225 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167
  17 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 288
  (Polychromatic418967fa.accept_14_2_1_8_1_650 16 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 225 288 3 5 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 225 288 (Polychromatic418967fa.accept_19_14_16_3_1_15089 14 225 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132
  13 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 225 288 3 4 75 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 225 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 225 288 (Polychromatic418967fa.accept_20_10_5_8_1_6385 10 225 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 225 288 9 1 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 225 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 225 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 225 288 3 2 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 225 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 225 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 288 (Polychromatic418967fa.accept_19_4_16_3_1_4175 4 225
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 225 288 3 1 75 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 225 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 225 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 288 (Polychromatic418967fa.accept_19_1_16_3_1_11223 1 225 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 225 288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 224 288 (Eq.refl Bool.true) (allA_succ_of_gcd 64 224 288 32 2 7 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 224 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 63 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 224 288 2 31 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 224 288 (accept_3_4 61 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 224 288 4 15 56 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 224 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 224 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 224 288 2 29 112 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 224 288
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 57 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 224 288 8 7 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 224 288 (accept_3_4 55 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  224 288 2 27 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 224 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 53 224 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 224 288 4 13 56 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 224 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470
  51 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 224 288 2 25 112 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 224 288
  (accept_3_4 49 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 224 288 16 3 14 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 224 288
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 47 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 224 288 2 23 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 224 288 (Polychromatic418967fa.accept_19_7_15_3_1_2896 45 224 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 224 288 4 11 56 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 224 288 (accept_3_4 43 224 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 224 288 2 21 112 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 224 288
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 41 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 224 288 8 5 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 224 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 224 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 224 288 2 19 112 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 224 288 (accept_3_4 37 224 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 224 288 4 9 56 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 224 288
  (Polychromatic418967fa.accept_13_9_3_2_1_399 35 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 224 288 2 17 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 224 288 (Polychromatic418967fa.accept_21_12_14_15_1_8909 33 224 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 224 288 32 1 7 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 224 288 (accept_3_4 31 224 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 224 288 2 15 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 224 288 (Polychromatic418967fa.accept_10_9_4_8_1_741
  29 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 224 288 4 7 56 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 224 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 224 288 2 13 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 224 288 (accept_3_4 25 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 224 288 8 3 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 224 288 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 224 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 224 288 2 11 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 224 288 (Polychromatic418967fa.accept_17_4_3_16_1_9483
  21 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 224 288 4 5 56 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 224 288
  (accept_3_4 19 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 224 288 2 9 112 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 224 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 17 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 224 288 16 1 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 224 288 (Polychromatic418967fa.accept_27_15_8_18_1_17842 15 224 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 224 288 2 7 112 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 224 288 (accept_3_4 13 224 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 224 288 4 3 56 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 224 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 11 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 224 288 2 5 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 224 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 224 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 224 288 8 1 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 224 288 (accept_3_4 7 224 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 224 288 2 3 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 224 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 5 224 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 224 288 4 1 56 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 224 288
  (Polychromatic418967fa.accept_21_3_14_15_1_10526 3 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 224 288 2 1 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 224 288 (accept_3_4 1 224 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 224 288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 223 288 (Eq.refl
  Bool.true) (allA_succ_of_accept 65 223 288 (accept_3_5 65 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 223 288 (Polychromatic418967fa.accept_19_7_14_3_1_1793 64 223 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 223 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 63 223
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 223 288 (accept_3_5 62 223
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 223 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 223 288 (Polychromatic418967fa.accept_21_18_13_15_1_2884 60 223 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 223 288 (accept_3_5 59 223 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 223 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 223 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 223 288
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 57 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 223 288 (accept_3_5 56 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 223 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 55 223 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 223 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 223 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 223 288 (accept_3_5 53 223 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 223 288
  (Polychromatic418967fa.accept_17_1_2_16_1_5596 52 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 223 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 223 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 223 288 (accept_3_5 50 223 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 223 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 49 223 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 223 288
  (Polychromatic418967fa.accept_17_14_2_16_1_4380 48 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 223 288 (accept_3_5 47 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 223 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 223 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 223 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 223
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 223 288 (accept_3_5 44 223
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 223 288
  (Polychromatic418967fa.accept_19_5_14_3_1_4187 43 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 223 288 (Polychromatic418967fa.accept_15_12_13_3_1_1915 42 223 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 223 288 (accept_3_5 41 223 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 223 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 223 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 223 288
  (Polychromatic418967fa.accept_15_9_13_3_1_535 39 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 223 288 (accept_3_5 38 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 223 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 223 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 223 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 223 288 (accept_3_5 35 223 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 223 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 223
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 223 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 223 288 (accept_3_5 32 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 223 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 223 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 223 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 223 288 (accept_3_5 29 223 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 223 288 (Polychromatic418967fa.accept_19_9_14_3_1_2912 28 223 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 223 288
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 223 288 (accept_3_5 26 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 223 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 223 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 223 288 (Polychromatic418967fa.accept_15_9_13_3_1_535 24 223
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 288 (accept_3_5 23 223
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 223 288
  (Polychromatic418967fa.accept_17_5_2_16_1_1294 22 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 223 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 223 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 223 288 (accept_3_5 20 223 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 223 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 223 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 223 288
  (Polychromatic418967fa.accept_17_1_2_16_1_5596 18 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 223 288 (accept_3_5 17 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 223 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 223 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 223 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 223 288 (accept_3_5 14 223 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 223 288 (Polychromatic418967fa.accept_20_13_3_8_1_4865 13 223
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 223 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 223 288 (accept_3_5 11 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 223 288 (Polychromatic418967fa.accept_15_10_13_3_1_4816 10 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 223 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 223 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 288 (accept_3_5 8 223 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 7 223 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 288 (accept_3_5 5 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 288 (Polychromatic418967fa.accept_23_4_16_12_1_17701 4 223 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 288 (Polychromatic418967fa.accept_30_3_13_18_1_17841 3 223 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 288 (accept_3_5 2 223 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 223 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 222 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 222 288 6 11 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 222 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 222 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 222 288 2 32 111 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 222 288 3 21 74 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 222 288 2 31 111 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 222 288
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 61 222 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 222 288 6 10 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 222 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 222 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 222 288 2 29 111 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 222 288 3 19 74 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 222 288 2 28 111 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 222 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 222 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 222 288 6 9 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 222 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 222 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 222 288 2 26 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 222 288 3 17 74 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 222 288 2 25 111 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 222 288
  (Polychromatic418967fa.accept_17_15_1_16_1_8166 49 222 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 222 288 6 8 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 222 288 (Polychromatic418967fa.accept_15_2_12_3_1_1183 47 222 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 222 288 2 23 111 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 222 288 3 15 74 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 222 288 2 22 111 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 222 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 43 222 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 222 288 6 7 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 222 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 222 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 222 288 2 20 111 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 222 288 3 13 74 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 222 288 2 19 111 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 222 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 37 222 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 222 288 6 6 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 222 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 222 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 222 288 2 17 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 222 288 3 11 74 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 222 288 2 16 111 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 222 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 222 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 222 288 6 5 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 222 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 29 222 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 222 288 2 14 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 222 288 3 9 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 222 288 2 13 111 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 222 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 222 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 288 6 4 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 222 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 222 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 222 288 2 11 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 222 288 3 7 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 222 288 2 10 111 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 222 288
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 222 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 288 6 3 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 222 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 222 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 222 288 2 8 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 222 288 3 5 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 222 288 2 7 111 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 222 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 222 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 288 6 2 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 222 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 222 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 222 288 2 5 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 222 288 3 3 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 222 288 2 4 111 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 222 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 288 6 1 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 222 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 222 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 288 2 2 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 222 288 3 1 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 222 288 2 1 111 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 288
  (Polychromatic418967fa.accept_21_1_12_15_1_2880 1 222 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 221 288 (Eq.refl
  Bool.true) (allA_succ_of_accept 67 221 288 (accept_3_4 67 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 221 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 221 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 221 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 65 221
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 221 288 (accept_3_4 64 221
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 221 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 63 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 221 288 (Polychromatic418967fa.accept_22_18_1_2_1_8505 62 221 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 221 288 (accept_3_4 61 221 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 221 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 60 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 221 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 221 288 (accept_3_4 58 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 221 288 (Polychromatic418967fa.accept_23_11_14_12_1_17840 57 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 56 221 288 (Polychromatic418967fa.accept_22_12_1_2_1_13238 56 221 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 221 288 (accept_3_4 55 221 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 221 288 (Polychromatic418967fa.accept_7_5_4_1_1_412
  54 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 221 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 53 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 221 288 (accept_3_4 52 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 221 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 221 288 (Polychromatic418967fa.accept_22_6_1_2_1_17735 50 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 221 288 (accept_3_4 49 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 221 288 (Polychromatic418967fa.accept_19_10_12_3_1_12558 48
  221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 221 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 221 288 (accept_3_4 46 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 221 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 221 288 (Polychromatic418967fa.accept_15_14_11_3_1_1957 44 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 221 288 (accept_3_4 43 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 221 288 (Polychromatic418967fa.accept_25_17_21_13_1_9067 42
  221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 221 288
  (Polychromatic418967fa.accept_26_15_13_2_1_17839 41 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 221 288 (accept_3_4 40 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 221 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 39 221 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 221 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 221 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 221 288 (accept_3_4 37 221 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 221 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063
  36 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 221 288
  (Polychromatic418967fa.accept_25_10_21_13_1_17838 35 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 221 288 (accept_3_4 34 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 221 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 221 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 221 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 221
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 221 288 (accept_3_4 31 221
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 221 288
  (Polychromatic418967fa.accept_19_11_12_3_1_8407 30 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 221 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 288 (accept_3_4 28 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 288 (Polychromatic418967fa.accept_20_7_1_8_1_10806 27 221
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 221 288 (accept_3_4 25 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 221 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 221 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 221 288 (accept_3_4 22 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 221 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 221
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 288
  (Polychromatic418967fa.accept_25_20_21_13_1_17690 20 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 221 288 (accept_3_4 19 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 221 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 221 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 221 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 221 288 (accept_3_4 16 221 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 288
  (Polychromatic418967fa.accept_19_15_12_3_1_11213 15 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 221 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 288 (accept_3_4 13 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 221 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 221 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 288
  (Polychromatic418967fa.accept_19_11_12_3_1_8407 11 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 221 288 (accept_3_4 10 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 221 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 221 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 288 (Polychromatic418967fa.accept_15_8_11_3_1_3847 8 221
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 288 (accept_3_4 7 221 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172
  6 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 221 288 (accept_3_4 4 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  221 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 221 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 221 288 (Polychromatic418967fa.accept_19_2_12_3_1_5446 2 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 288 (accept_3_4 1 221 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 221 288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 69 220 288 (Eq.refl Bool.true) (allA_succ_of_gcd 68 220 288 4 17 55 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 220 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 67 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 220 288 2 33 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 220 288 (accept_3_5 65 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 220 288 4 16 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 220 288 (Polychromatic418967fa.accept_27_9_4_18_1_17837 63 220 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 220 288 2 31 110 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 220 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 220 288 4 15 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 220 288 (accept_3_5 59 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 220 288 2 29 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 220 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 57 220 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 220 288 4 14 55 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 220 288
  (Polychromatic418967fa.accept_13_3_12_2_1_385 55 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 220 288 2 27 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 220 288 (accept_3_5 53 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 220 288 4 13 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 220 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 220 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 220 288 2 25 110 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 220 288
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 49 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 220 288 4 12 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 220 288 (accept_3_5 47 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 220 288 2 23 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 220 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 45 220 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 220 288 4 11 55 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 220 288
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 43 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 220 288 2 21 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 220 288 (accept_3_5 41 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 220 288 4 10 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 220 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 220 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 220 288 2 19 110 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 220 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 220 288 4 9 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 220 288 (accept_3_5 35 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  220 288 2 17 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 220 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 220 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 220 288 4 8 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 220 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423
  31 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 220 288 2 15 110 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 220 288
  (accept_3_5 29 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 220 288 4 7 55 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 220 288
  (Polychromatic418967fa.accept_13_1_12_2_1_384 27 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 220 288 2 13 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 220 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 220 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 220 288 4 6 55 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 220 288 (accept_3_5 23 220 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 220 288 2 11 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 220 288 (Polychromatic418967fa.accept_15_6_10_3_1_2844
  21 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 220 288 4 5 55 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 220 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 220 288 2 9 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 220 288 (accept_3_5 17 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 220 288 4 4 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 220 288 (Polychromatic418967fa.accept_25_15_20_13_1_753 15 220 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 220 288 2 7 110 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 220 288
  (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 220 288 4 3 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 220 288 (accept_3_5 11 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 220 288 2 5 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 220 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 220 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 220 288 4 2 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 220 288 (Polychromatic418967fa.accept_15_7_10_3_1_2891
  7 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 220 288 2 3 110 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 220 288
  (accept_3_5 5 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 220 288 4 1 55 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 220 288
  (Polychromatic418967fa.accept_13_3_12_2_1_385 3 220 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 220 288 2 1 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 220 288 (Polychromatic418967fa.accept_13_1_12_2_1_384 1 220 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 219 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 219 288 3 23 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 219 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 68 219 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 219 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 67 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 219 288 3 22 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 219 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 65 219 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 219 288 (Polychromatic418967fa.accept_10_4_9_8_1_125
  64 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 219 288 3 21 73 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 219 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 219 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 61 219 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 219 288 3 20 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 219 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 59
  219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 219 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 58 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 219 288 3 19 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 219 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 56 219 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 219 288 (Polychromatic418967fa.accept_7_6_2_1_1_214
  55 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 219 288 3 18 73 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 219 288
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 53 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 219 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 219 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 219 288 3 17 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 219 288 (Polychromatic418967fa.accept_15_5_9_3_1_528
  50 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 219 288
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 49 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 219 288 3 16 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 219 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 219 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 219 288
  (Polychromatic418967fa.accept_21_4_9_15_1_11925 46 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 219 288 3 15 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 219 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 219 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 219 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 43 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 219 288 3 14 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 219 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 219 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 219 288
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 40 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 219 288 3 13 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 219 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 219 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135
  37 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 219 288 3 12 73 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 219 288
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 219 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 219 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 219 288 3 11 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 219 288
  (Polychromatic418967fa.accept_19_13_10_3_1_11235 32 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 219 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 219 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 219 288 3 10 73 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 219 288
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 219 288 (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 219 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 219 288 3 9 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 219 288 (Polychromatic418967fa.accept_19_7_10_3_1_4149
  26 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 288
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 219 288 3 8 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 219 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 219 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 22 219
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 219 288 3 7 73 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 219 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 219 288 (Polychromatic418967fa.accept_21_19_9_15_1_4217 19 219 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 219 288 3 6 73 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 219 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 219 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 219 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 219 288 3 5 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 219 288 (Polychromatic418967fa.accept_10_4_9_8_1_125
  14 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 219 288 3 4 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 219 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 219 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 219 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 219 288 3 3 73 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 219 288
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 219 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 219 288 3 2 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 219 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 219 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 4 219 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 219 288 3 1 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 219 288 (Polychromatic418967fa.accept_21_2_9_15_1_5747 2 219 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 219 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 218 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 218 288 2 35 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 218 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 69 218 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 218 288 2 34 109 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 218 288 (accept_3_4 67 218 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 218 288 2 33 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 218 288 (Polychromatic418967fa.accept_15_5_8_3_1_556
  65 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 218 288 2 32 109 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 218 288
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 218 288 2 31 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 218 288 (accept_3_4 61 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 218 288 2 30 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 218 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 59 218 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 218 288 2 29 109 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 218 288
  (Polychromatic418967fa.accept_13_5_10_2_1_856 57 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 218 288 2 28 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 218 288 (accept_3_4 55 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 218 288 2 27 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 218 288 (Polychromatic418967fa.accept_17_2_14_16_1_2187 53 218 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 218 288 2 26 109 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 218 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 51 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 218 288 2 25 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 218 288 (accept_3_4 49 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 218 288 2 24 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 218 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 47 218 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 218 288 2 23 109 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 218 288
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 218 288 2 22 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 218 288 (accept_3_4 43 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 218 288 2 21 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 218 288 (Polychromatic418967fa.accept_15_11_8_3_1_1943 41 218 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 218 288 2 20 109 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 218 288
  (Polychromatic418967fa.accept_15_9_8_3_1_557 39 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 218 288 2 19 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 218 288 (accept_3_4 37 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 218 288 2 18 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 218 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 35 218 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 218 288 2 17 109 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 218 288
  (Polychromatic418967fa.accept_19_14_9_3_1_13821 33 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 218 288 2 16 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 218 288 (accept_3_4 31 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 218 288 2 15 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 218 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 218 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 218 288 2 14 109 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 218 288
  (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 218 288 2 13 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 218 288 (accept_3_4 25 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 218 288 2 12 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 218 288 (Polychromatic418967fa.accept_20_3_18_8_1_4859 23 218 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 218 288 2 11 109 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 218 288
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 218 288 2 10 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 218 288 (accept_3_4 19 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 218 288 2 9 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 218 288 (Polychromatic418967fa.accept_21_17_8_15_1_10549 17 218 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 218 288 2 8 109 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 218 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 15 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 218 288 2 7 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 218 288 (accept_3_4 13 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 218 288 2 6 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 218 288 (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 218 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 218 288 2 5 109 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 218 288
  (Polychromatic418967fa.accept_15_9_8_3_1_557 9 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 218 288 2 4 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 218 288 (accept_3_4 7 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 218 288 2 3 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 218 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 5 218 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 218 288 2 2 109 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 218 288
  (Polychromatic418967fa.accept_13_3_10_2_1_381 3 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 218 288 2 1 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 218 288 (accept_3_4 1 218 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 217 288 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 217 288 (accept_3_5 71 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 217 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 70 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 217 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 217 288 (accept_3_5 68 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 217 288 (Polychromatic418967fa.accept_20_7_17_8_1_3452 67 217
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 217 288
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 66 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 217 288 (accept_3_5 65 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 217 288 (Polychromatic418967fa.accept_15_4_7_3_1_119 64 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 217 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 217 288 (accept_3_5 62 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 217 288 (Polychromatic418967fa.accept_19_4_8_3_1_8416 61 217
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 217 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 60 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 217 288 (accept_3_5 59 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 217 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 58 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 217 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 57 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 217 288 (accept_3_5 56 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 217 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 55 217
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 217 288
  (Polychromatic418967fa.accept_17_3_13_16_1_2183 54 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 217 288 (accept_3_5 53 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 217 288 (Polychromatic418967fa.accept_19_14_8_3_1_6981 52 217 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 217 288 (Polychromatic418967fa.accept_19_13_8_3_1_2906 51 217
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 217 288 (accept_3_5 50 217
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 217 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 217 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 48 217 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 217 288 (accept_3_5 47 217 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 217 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 46 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 217 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 217 288 (accept_3_5 44 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 217 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 43 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 217 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 42 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 217 288 (accept_3_5 41 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 217 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 40 217
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 217 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 217 288 (accept_3_5 38 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 217 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 37 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 217 288 (Polychromatic418967fa.accept_19_17_8_3_1_11211 36 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 217 288 (accept_3_5 35 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 217 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 34 217
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 217 288
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 33 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 217 288 (accept_3_5 32 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 217 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 217 288 (Polychromatic418967fa.accept_19_11_8_3_1_862 30 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 217 288 (accept_3_5 29 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 217 288 (Polychromatic418967fa.accept_22_6_19_2_1_6814 28 217
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 217 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 217 288 (accept_3_5 26 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 217 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 217 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 217 288 (accept_3_5 23 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 217 288 (Polychromatic418967fa.accept_21_1_7_15_1_4259 22 217
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 217 288
  (Polychromatic418967fa.accept_22_21_19_2_1_17836 21 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 217 288 (accept_3_5 20 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 217 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 217 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 217 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 217
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 217 288 (accept_3_5 17 217
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 217 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 16 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 217 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 217 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 288 (accept_3_5 14 217 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 217 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 13 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 288
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 288 (accept_3_5 11 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 288 (Polychromatic418967fa.accept_15_10_7_3_1_1939 10 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 217 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 288 (accept_3_5 8 217 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 288
  (Polychromatic418967fa.accept_13_6_9_2_1_838 6 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 288 (accept_3_5 5 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 288 (Polychromatic418967fa.accept_15_4_7_3_1_119 4 217 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 217 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 288 (accept_3_5 2 217 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 217 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 216 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 216 288 72 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 216 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 71 216 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 216 288 2 35 108 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 216 288 3 23 72 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 216 288 4 17 54 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 216 288
  (Polychromatic418967fa.accept_19_10_7_3_1_6977 67 216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 216 288 6 11 36 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 216 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 216 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 216 288 8 8 27 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 216 288 9 7 24 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 216 288 2 31 108 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 216 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 216 288 12 5 18 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 216 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 59 216 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 216 288 2 29 108 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 216 288 3 19 72 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 216 288 8 7 27 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 216 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 55 216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 216 288 18 3 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 216 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 216 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 216 288 4 13 54 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 216 288 3 17 72 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 216 288 2 25 108 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 216 288
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 49 216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 216 288 24 2 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 216 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 216 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 216 288 2 23 108 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 216 288 9 5 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 216 288 4 11 54 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 216 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 216 288 6 7 36 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 216 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 41 216 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 216 288 8 5 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 216 288 3 13 72 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 216 288 2 19 108 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 216 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 216 288 36 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 216 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 216 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 216 288 2 17 108 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 216 288 3 11 72 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 216 288 8 4 27 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 216 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 216 288 6 5 36 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 216 288 (Polychromatic418967fa.accept_19_10_7_3_1_6977 29 216 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 216 288 4 7 54 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 216 288 9 3 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 216 288 2 13 108 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 216 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 216 288 24 1 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 216 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 216 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 216 288 2 11 108 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 216 288 3 7 72 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 216 288 4 5 54 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 216 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 19
  216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 216 288 18 1 12 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 216 288
  (Polychromatic418967fa.accept_21_17_6_15_1_5765 17 216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 216 288 8 2 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 216 288 3 5 72 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 216 288 2 7 108 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 216 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 216
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 288 12 1 18 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 288
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 216 288 2 5 108 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 216 288 9 1 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 216 288 8 1 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 216 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 216 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 288 6 1 36 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 5
  216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 288 4 1 54 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 216 288 3 1 72 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 216 288 2 1 108 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 288
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 216 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 216 288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 215 288
  (Eq.refl Bool.true) (allA_succ_of_accept 73 215 288 (accept_3_4 73 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 215 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 215 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 215 288 (Polychromatic418967fa.accept_21_8_5_15_1_4208 71 215
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 215 288 (accept_3_4 70 215
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 215 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 215 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 68 215 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 215 288 (accept_3_4 67 215 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 215 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 215 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 215 288
  (Polychromatic418967fa.accept_17_14_11_16_1_3261 65 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 215 288 (accept_3_4 64 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 215 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 215 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 215 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 62 215 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 215 288 (accept_3_4 61 215 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 215 288 (Polychromatic418967fa.accept_7_4_5_1_1_418
  60 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 215 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 215 288 (accept_3_4 58 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 215 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 57 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 215 288 (Polychromatic418967fa.accept_17_5_11_16_1_3257 56 215 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 215 288 (accept_3_4 55 215 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 215 288 (Polychromatic418967fa.accept_15_9_5_3_1_554 54 215
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 215 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 215 288 (accept_3_4 52 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 215 288 (Polychromatic418967fa.accept_15_6_5_3_1_1988 51 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 215 288 (Polychromatic418967fa.accept_20_10_15_8_1_4818 50 215 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 215 288 (accept_3_4 49 215 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 215 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 215 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 215 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 215 288 (accept_3_4 46 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 215 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 215 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 44 215 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 215 288 (accept_3_4 43 215 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 215 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 215
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 215 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 215 288 (accept_3_4 40 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 215 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 215 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 215 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 288 (accept_3_4 37 215 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 215 288 (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 215 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 215 288
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 215 288 (accept_3_4 34 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 215 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 215 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 215 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 288 (accept_3_4 31 215 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 215 288 (Polychromatic418967fa.accept_20_10_15_8_1_4818 30 215 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 215 288
  (Polychromatic418967fa.accept_17_12_11_16_1_6903 29 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 215 288 (accept_3_4 28 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 215 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 215 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 215 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 26 215 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 215 288 (accept_3_4 25 215 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 215 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 24
  215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 215 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 215 288 (accept_3_4 22 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 215 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 215 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 215 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 288 (accept_3_4 19 215 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 215 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 215 288 (accept_3_4 16 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 215 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 215 288 (Polychromatic418967fa.accept_17_14_11_16_1_3261 14 215 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 288 (accept_3_4 13 215 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 215
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 215 288 (accept_3_4 10 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  215 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 215 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 215 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 288 (accept_3_4 7 215 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 215 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 288
  (Polychromatic418967fa.accept_13_5_7_2_1_852 5 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 215 288 (accept_3_4 4 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  215 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 215 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 215 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 215 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 288 (accept_3_4 1 215 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 215 288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 75 214 288 (Eq.refl Bool.true) (allA_succ_of_gcd 74 214 288 2 37 107 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 214 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 214 288 2 36 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 214 288 (accept_3_5 71 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 214 288 2 35 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 214 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 69 214 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 214 288 2 34 107 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 214 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 67 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 214 288 2 33 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 214 288 (accept_3_5 65 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 214 288 2 32 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 214 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 214 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 214 288 2 31 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 214 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 61 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 214 288 2 30 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 214 288 (accept_3_5 59 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 214 288 2 29 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 214 288 (Polychromatic418967fa.accept_17_6_10_16_1_9453 57 214 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 214 288 2 28 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 214 288
  (Polychromatic418967fa.accept_19_17_5_3_1_5455 55 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 214 288 2 27 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 214 288 (accept_3_5 53 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 214 288 2 26 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 214 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 51 214 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 214 288 2 25 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 214 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 214 288 2 24 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 214 288 (accept_3_5 47 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 214 288 2 23 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 214 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 214 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 214 288 2 22 107 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 214 288
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 43 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 214 288 2 21 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 214 288 (accept_3_5 41 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 214 288 2 20 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 214 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 214 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 214 288 2 19 107 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 214 288
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 37 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 214 288 2 18 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 214 288 (accept_3_5 35 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 214 288 2 17 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 214 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 214 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 214 288 2 16 107 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 214 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 214 288 2 15 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 214 288 (accept_3_5 29 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 214 288 2 14 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 214 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 214 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 214 288 2 13 107 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 214 288
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 25 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 214 288 2 12 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 214 288 (accept_3_5 23 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 214 288 2 11 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 214 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 214 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 214 288 2 10 107 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 214 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 214 288 2 9 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 214 288 (accept_3_5 17 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 214 288 2 8 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 214 288 (Polychromatic418967fa.accept_20_15_14_8_1_9344 15 214 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 214 288 2 7 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 214 288
  (Polychromatic418967fa.accept_20_13_14_8_1_4850 13 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 214 288 2 6 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 214 288 (accept_3_5 11 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 214 288 2 5 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 214 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 214 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 288 2 4 107 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 288
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 288 2 3 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 288 (accept_3_5 5 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 288 2 2 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 214 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 288 2 1 107 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 288
  (Polychromatic418967fa.accept_13_1_6_2_1_377 1 214 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 213 288
  (Eq.refl Bool.true) (allA_succ_of_gcd 75 213 288 3 25 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 213 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 213 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 213 288
  (Polychromatic418967fa.accept_19_16_4_3_1_2946 73 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 213 288 3 24 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 213 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 71 213 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 213 288
  (Polychromatic418967fa.accept_19_13_4_3_1_2945 70 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 213 288 3 23 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 213 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 213 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 213 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 67
  213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 213 288 3 22 71 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 213 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 213 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 64 213 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 213 288 3 21 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 213 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477
  62 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 213 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 213 288 3 20 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 213 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 59 213 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 213 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 58
  213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 213 288 3 19 71 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 213 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 213 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 55 213 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 213 288 3 18 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 213 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 213 288
  (Polychromatic418967fa.accept_21_10_3_15_1_13463 52 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 213 288 3 17 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 213 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 50 213 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 288
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 49 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 213 288 3 16 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 213 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 213 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 213 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 46
  213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 213 288 3 15 71 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 213 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 213 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 43 213 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 213 288 3 14 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 213 288 (Polychromatic418967fa.accept_10_1_3_8_1_136
  41 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 213 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 40 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 213 288 3 13 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 213 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 38 213 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 213 288 3 12 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 213 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 213 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 288
  (Polychromatic418967fa.accept_20_14_13_8_1_4847 34 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 213 288 3 11 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 213 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 213 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 31 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 213 288 3 10 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 213 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 213 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 28 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 213 288 3 9 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 213 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 213 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 213 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 213 288 3 8 71 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 213 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 22 213 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 213 288 3 7 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 213 288 (Polychromatic418967fa.accept_11_9_4_2_1_600
  20 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 213 288 3 6 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 213 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 213 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 213 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 213 288 3 5 71 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 213 288
  (Polychromatic418967fa.accept_20_14_13_8_1_4847 14 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 213 288 (Polychromatic418967fa.accept_17_13_9_16_1_3254 13 213 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 213 288 3 4 71 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 213 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477 10 213 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 213 288 3 3 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 213 288 (Polychromatic418967fa.accept_17_8_9_16_1_6844 8 213 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 288
  (Polychromatic418967fa.accept_13_7_5_2_1_401 7 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 213 288 3 2 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 213 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 213 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 213 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 213 288 3 1 71 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 213 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 213 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 213 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 213
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 212 288 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 212 288 4 19 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 212 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 75 212 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 212 288 2 37 106 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 212 288 (accept_3_4 73 212 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 212 288 4 18 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 212 288
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 71 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 212 288 2 35 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 212 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 212 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 212 288 4 17 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 212 288 (accept_3_4 67 212 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 212 288 2 33 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 212 288 (Polychromatic418967fa.accept_10_5_2_8_1_135
  65 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 212 288 4 16 53 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 212 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 63 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 212 288 2 31 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 212 288 (accept_3_4 61 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 212 288 4 15 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 212 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 212 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 212 288 2 29 106 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 212 288
  (Polychromatic418967fa.accept_13_5_4_2_1_846 57 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 212 288 4 14 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 212 288 (accept_3_4 55 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 212 288 2 27 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 212 288 (Polychromatic418967fa.accept_17_2_8_16_1_4403 53 212 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 212 288 4 13 53 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 212 288
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 51 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 212 288 2 25 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 212 288 (accept_3_4 49 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 212 288 4 12 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 212 288 (Polychromatic418967fa.accept_22_3_14_2_1_13240 47 212 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 212 288 2 23 106 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 212 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 212 288 4 11 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 212 288 (accept_3_4 43 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 212 288 2 21 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 212 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 212 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 212 288 4 10 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 212 288
  (Polychromatic418967fa.accept_21_18_2_15_1_5737 39 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 212 288 2 19 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 212 288 (accept_3_4 37 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 212 288 4 9 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 212 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 212 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 212 288 2 17 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 212 288
  (Polychromatic418967fa.accept_22_11_14_2_1_11700 33 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 212 288 4 8 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 212 288 (accept_3_4 31 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 212 288 2 15 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 212 288 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 212 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 212 288 4 7 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 212 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 212 288 2 13 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 212 288 (accept_3_4 25 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 212 288 4 6 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 212 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 212 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 212 288 2 11 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 212 288
  (Polychromatic418967fa.accept_22_21_14_2_1_2227 21 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 212 288 4 5 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 212 288 (accept_3_4 19 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 212 288 2 9 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 212 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 212 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 212 288 4 4 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 212 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 212 288 2 7 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 212 288 (accept_3_4 13 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 212 288 4 3 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 212 288 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 212 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 288 2 5 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 288 (Polychromatic418967fa.accept_17_9_8_16_1_2176
  9 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 212 288 4 2 53 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 212 288 (accept_3_4 7
  212 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 212 288 2 3 106 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 212 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 5 212 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 212 288 4 1 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 212 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 212 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 212 288 2 1 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 212 288 (accept_3_4 1 212 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 212 288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 78 211 288 (Eq.refl Bool.true) (allA_succ_of_accept 77 211 288 (accept_3_5 77 211 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 211 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 76 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 211 288
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 75 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 211 288 (accept_3_5 74 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 211 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 73 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 211 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 72 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 211 288 (accept_3_5 71 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 211 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 70 211
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 211 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 69 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 211 288 (accept_3_5 68 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 211 288 (Polychromatic418967fa.accept_27_13_22_18_1_6230 67 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 211 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 66 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 211 288 (accept_3_5 65 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 211 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 64 211
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 211 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 63 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 211 288 (accept_3_5 62 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 211 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 61 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 211 288 (Polychromatic418967fa.accept_21_18_1_15_1_11930 60 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 211 288 (accept_3_5 59 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 211 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 58 211
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 211 288
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 57 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 211 288 (accept_3_5 56 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 211 288 (Polychromatic418967fa.accept_19_17_2_3_1_4190 55 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 211 288 (Polychromatic418967fa.accept_17_3_7_16_1_3251 54 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 211 288 (accept_3_5 53 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 211 288 (Polychromatic418967fa.accept_21_10_1_15_1_10541 52
  211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 211 288
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 51 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 211 288 (accept_3_5 50 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 211 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 211 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 48 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 211 288 (accept_3_5 47 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 211 288 (Polychromatic418967fa.accept_28_18_15_8_1_17835 46
  211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 211 288
  (Polychromatic418967fa.accept_21_3_1_15_1_4287 45 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 211 288 (accept_3_5 44 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 211 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 43 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 211 288 (Polychromatic418967fa.accept_17_8_7_16_1_9508 42 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 211 288 (accept_3_5 41 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 211 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 40 211
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 211 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 39 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 211 288 (accept_3_5 38 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 211 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 37 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 211 288 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 211 288 (accept_3_5 35 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 211 288 (Polychromatic418967fa.accept_15_4_1_3_1_1922 34 211
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 211 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 33 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 211 288 (accept_3_5 32 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 211 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 31 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 211 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 30 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 211 288 (accept_3_5 29 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 211 288 (Polychromatic418967fa.accept_15_13_1_3_1_1972 28 211
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 211 288 (accept_3_5 26 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 211 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 25 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 211 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 288 (accept_3_5 23 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 211 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 22 211
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 288
  (Polychromatic418967fa.accept_14_7_1_8_1_2873 21 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 211 288 (accept_3_5 20 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 211 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 211 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 288 (accept_3_5 17 211 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 16 211
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 288
  (Polychromatic418967fa.accept_22_15_13_2_1_13218 15 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 211 288 (accept_3_5 14 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 211 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 211 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 211
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 288 (accept_3_5 11 211
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 288
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 10 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 211 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 211 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 288 (accept_3_5 8 211 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 211 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873 7 211 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 288 (Polychromatic418967fa.accept_15_6_1_3_1_2852
  6 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 288 (accept_3_5 5
  211 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 288
  (Polychromatic418967fa.accept_15_4_1_3_1_1922 4 211 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 211 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 211 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 288 (accept_3_5 2 211 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 211 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 211 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 210 288 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 210 288 6 13 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 210 288 (Polychromatic418967fa.accept_17_9_6_16_1_3280 77 210 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 210 288 2 38 105 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 210 288 3 25 70 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 210 288 2 37 105 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 210 288
  (Polychromatic418967fa.accept_19_16_1_3_1_7007 73 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 210 288 6 12 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 210 288 (Polychromatic418967fa.accept_22_5_12_2_1_16279 71 210 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 210 288 2 35 105 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 210 288 3 23 70 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 210 288 2 34 105 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 210 288
  (Polychromatic418967fa.accept_19_10_1_3_1_12548 67 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 210 288 6 11 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 210 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 65 210 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 210 288 2 32 105 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 210 288 3 21 70 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 210 288 2 31 105 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 210 288
  (Polychromatic418967fa.accept_17_10_6_16_1_6862 61 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 210 288 6 10 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 210 288 (Polychromatic418967fa.accept_19_2_1_3_1_11216 59 210 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 210 288 2 29 105 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 210 288 3 19 70 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 210 288 2 28 105 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 210 288
  (Polychromatic418967fa.accept_19_17_1_3_1_4160 55 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 210 288 6 9 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 210 288 (Polychromatic418967fa.accept_25_3_10_13_1_17834 53 210 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 210 288 2 26 105 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 210 288 3 17 70 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 210 288 2 25 105 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 210 288
  (Polychromatic418967fa.accept_19_11_1_3_1_5555 49 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 210 288 6 8 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 210 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 47 210 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 210 288 2 23 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 210 288 3 15 70 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 210 288 2 22 105 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 210 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 210 288 6 7 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 210 288 (Polychromatic418967fa.accept_17_7_6_16_1_2195 41 210 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 210 288 2 20 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 210 288 3 13 70 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 210 288 2 19 105 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 210 288
  (Polychromatic418967fa.accept_20_17_10_8_1_9374 37 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 210 288 6 6 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 210 288 (Polychromatic418967fa.accept_19_16_1_3_1_7007 35 210 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 210 288 2 17 105 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 210 288 3 11 70 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 210 288 2 16 105 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 210 288
  (Polychromatic418967fa.accept_29_2_7_27_1_17833 31 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 210 288 6 5 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 210 288 (Polychromatic418967fa.accept_19_10_1_3_1_12548 29 210 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 210 288 2 14 105 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 210 288 3 9 70 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 210 288 2 13 105 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 210 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 210 288 6 4 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 210 288 (Polychromatic418967fa.accept_19_4_1_3_1_15091 23 210 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 210 288 2 11 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 210 288 3 7 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 210 288 2 10 105 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 288
  (Polychromatic418967fa.accept_22_19_12_2_1_14721 19 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 210 288 6 3 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 210 288 (Polychromatic418967fa.accept_19_17_1_3_1_4160 17 210 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 210 288 2 8 105 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 210 288 3 5 70 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 210 288 2 7 105 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 288
  (Polychromatic418967fa.accept_23_13_3_12_1_17676 13 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 210 288 6 2 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 210 288 (Polychromatic418967fa.accept_19_11_1_3_1_5555 11 210 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 288 2 5 105 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 210 288 3 3 70 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 210 288 2 4 105 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 288
  (Polychromatic418967fa.accept_17_7_6_16_1_2195 7 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 288 6 1 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 210 288 (Polychromatic418967fa.accept_19_5_1_3_1_8421 5 210 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 210 288 2 2 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 210 288 3 1 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 210 288 2 1 105 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 288
  (Polychromatic418967fa.accept_22_1_12_2_1_11707 1 210 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 209
  288 (Eq.refl Bool.true) (allA_succ_of_accept 79 209 288 (accept_3_4 79 209 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 209 288 (Polychromatic418967fa.accept_27_24_20_18_1_17755 78 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 209 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 77 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 209 288 (accept_3_4 76 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 209 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 209 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 74 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 209 288 (accept_3_4 73 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 209 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 209 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 209 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 71 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 209 288 (accept_3_4 70 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 209 288 (Polychromatic418967fa.accept_17_1_5_16_1_5589 69 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 209 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 209 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 209 288 (accept_3_4 67 209 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 209 288 (Polychromatic418967fa.accept_26_14_1_2_1_10584 66 209 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 209 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 209 288 (accept_3_4 64 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 209 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 63 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 209 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 62 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 209 288 (accept_3_4 61 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 209 288 (Polychromatic418967fa.accept_21_18_20_15_1_8916 60
  209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 209 288
  (Polychromatic418967fa.accept_20_19_9_8_1_12192 59 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 209 288 (accept_3_4 58 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 209 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 209 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 209 288 (Polychromatic418967fa.accept_15_11_14_3_1_1965 56 209
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 209 288 (accept_3_4 55 209
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 209 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 209 288 (Polychromatic418967fa.accept_17_2_5_16_1_1264 53 209 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 209 288 (accept_3_4 52 209 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 209 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 209 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 209 288
  (Polychromatic418967fa.accept_22_6_11_2_1_11698 50 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 209 288 (accept_3_4 49 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 209 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 48 209 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 209 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 209 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 209 288 (accept_3_4 46 209 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 209 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464
  45 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 209 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 209 288 (accept_3_4 43 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 209 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 42 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 209 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 41 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 209 288 (accept_3_4 40 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 209 288 (Polychromatic418967fa.accept_20_19_9_8_1_12192 39 209
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 209 288
  (Polychromatic418967fa.accept_13_12_1_2_1_845 38 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 209 288 (accept_3_4 37 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 209 288 (Polychromatic418967fa.accept_17_2_5_16_1_1264 36 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 209 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 35 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 209 288 (accept_3_4 34 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 209 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 209 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 209 288
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 32 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 209 288 (accept_3_4 31 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 209 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 209 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 29 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 209 288 (accept_3_4 28 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 209 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 209
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 209 288 (accept_3_4 25 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 209 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 209 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 209 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 288 (accept_3_4 22 209 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 209 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 288
  (Polychromatic418967fa.accept_22_20_11_2_1_16259 20 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 209 288 (accept_3_4 19 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 209 288 (Polychromatic418967fa.accept_17_1_5_16_1_5589 18 209 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 209
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 288 (accept_3_4 16 209
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 288
  (Polychromatic418967fa.accept_25_15_9_13_1_17681 15 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 209 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 288 (accept_3_4 13 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 209 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 11 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 209 288 (accept_3_4 10 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  209 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 209 288 (Polychromatic418967fa.accept_22_8_11_2_1_3507 8 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 288 (accept_3_4 7 209 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 209 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 288 (accept_3_4 4 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 209 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 209 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 288 (accept_3_4 1 209 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 81 208 288 (Eq.refl Bool.true) (allA_succ_of_gcd 80 208 288 16 5 13 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 208 288
  (Polychromatic418967fa.accept_22_13_10_2_1_5206 79 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 208 288 2 39 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 208 288 (accept_3_5 77 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 208 288 4 19 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 208 288 (Polychromatic418967fa.accept_21_12_19_15_1_8942 75 208 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 208 288 2 37 104 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 208 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 208 288 8 9 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 208 288 (accept_3_5 71 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  208 288 2 35 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 208 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 208 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 208 288 4 17 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 208 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 67
  208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 208 288 2 33 104 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 208 288
  (accept_3_5 65 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 208 288 16 4 13 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 208 288
  (Polychromatic418967fa.accept_19_6_18_3_1_11230 63 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 208 288 2 31 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 208 288 (Polychromatic418967fa.accept_15_1_13_3_1_2002 61 208 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 208 288 4 15 52 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 208 288 (accept_3_5 59 208 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 208 288 2 29 104 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 208 288
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 57 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 208 288 8 7 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 208 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 208 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 208 288 2 27 104 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 208 288 (accept_3_5 53 208 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 208 288 4 13 52 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 208 288
  (Polychromatic418967fa.accept_21_9_19_15_1_5782 51 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 208 288 2 25 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 208 288 (Polychromatic418967fa.accept_17_15_4_16_1_6890 49 208 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 208 288 16 3 13 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 208 288 (accept_3_5 47
  208 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 208 288 2 23 104 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 208 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 208 288 4 11 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 208 288 (Polychromatic418967fa.accept_21_1_19_15_1_8914 43 208 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 208 288 2 21 104 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 208 288 (accept_3_5 41 208 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 208 288 8 5 26 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 208 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 208 288 2 19 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 208 288 (Polychromatic418967fa.accept_17_3_4_16_1_3208 37 208 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 208 288 4 9 52 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 208 288 (accept_3_5 35 208 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 208 288 2 17 104 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 208 288
  (Polychromatic418967fa.accept_19_14_18_3_1_12569 33 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 208 288 16 2 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 208 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 208 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 208 288 2 15 104 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 208 288 (accept_3_5 29 208 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 208 288 4 7 52 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 208 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 208 288 2 13 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 208 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 208 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 208 288 8 3 26 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 208 288 (accept_3_5 23 208 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 208 288 2 11 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 208 288 (Polychromatic418967fa.accept_19_2_18_3_1_5517
  21 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 208 288 4 5 52 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 208 288
  (Polychromatic418967fa.accept_25_19_8_13_1_10799 19 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 208 288 2 9 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 208 288 (accept_3_5 17 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 208 288 16 1 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 208 288 (Polychromatic418967fa.accept_17_15_4_16_1_6890 15 208 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 208 288 2 7 104 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 208 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 208 288 4 3 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 208 288 (accept_3_5 11 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  208 288 2 5 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 208 288 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 208 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 208 288 8 1 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 208 288 (Polychromatic418967fa.accept_21_7_19_15_1_4201 7 208
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 208 288 2 3 104 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 288 (accept_3_5 5
  208 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 288 4 1 52 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 208 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 208 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 208 288 2 1 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 208 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 208 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 207 288 (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 207 288 9 9 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 207 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 207 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 207 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184
  79 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 207 288 3 26 69 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 207 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 77 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 207 288 (Polychromatic418967fa.accept_21_13_18_15_1_2837 76 207 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 207 288 3 25 69 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 207 288
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 74 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 207 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 207 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 207 288 9 8 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 207 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707
  71 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 207 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 70 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 207 288 3 23 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 207 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 207 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 207 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 67 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 207 288 3 22 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 207 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 207 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 207 288
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 64 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 207 288 9 7 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 207 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 62 207 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 207 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 61 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 207 288 3 20 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 207 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 207 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 207 288
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 58 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 207 288 3 19 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 207 288 (Polychromatic418967fa.accept_13_4_12_2_1_1459 56 207 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 207 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 55 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 207 288 9 6 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 207 288 (Polychromatic418967fa.accept_13_1_12_2_1_384 53 207 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 207 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 207 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 207 288 3 17 69 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 207 288
  (Polychromatic418967fa.accept_19_12_17_3_1_5515 50 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 207 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 207 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 207 288 3 16 69 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 207 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 207 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 46 207 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 207 288 9 5 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 207 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423
  44 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 288
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 43 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 207 288 3 14 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 207 288 (Polychromatic418967fa.accept_17_7_3_16_1_2208 41 207 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 207 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 40 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 207 288 3 13 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 207 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 207 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 288 (Polychromatic418967fa.accept_11_4_9_2_1_259
  37 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 207 288 9 4 23 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 207 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 288 (Polychromatic418967fa.accept_19_15_17_3_1_13760 34 207 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 207 288 3 11 69 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 207 288
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 32 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 207 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 207 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 207 288 3 10 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 207 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184
  29 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 28 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 207 288 9 3 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 207 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 207 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 207 288 3 8 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 207 288 (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 207 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 22 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 207 288 3 7 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 207 288 (Polychromatic418967fa.accept_19_1_17_3_1_1821 20 207 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 207 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 207 288 9 2 23 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 207 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 16 207 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 207 288 3 5 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 207 288 (Polychromatic418967fa.accept_13_1_12_2_1_384
  14 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 207 288 3 4 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 207 288 (Polychromatic418967fa.accept_22_11_9_2_1_16266 11 207 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 10 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 207 288 9 1 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 207 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 207 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 207 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 207 288 3 2 69 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 207 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 207 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 207 288 3 1 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 207 288 (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 207 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 288
  (Polychromatic418967fa.accept_13_1_12_2_1_384 1 207 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 207 288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 206
  288 (Eq.refl Bool.true) (allA_succ_of_gcd 82 206 288 2 41 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 206 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 206 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 206 288 2 40 103 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 206 288 (accept_3_4 79
  206 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 206 288 2 39 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 206 288
  (Polychromatic418967fa.accept_19_1_16_3_1_11223 77 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 206 288 2 38 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 206 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 206 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 206 288 2 37 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 206 288 (accept_3_4 73 206 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 206 288 2 36 103 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 206 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 71 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 206 288 2 35 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 206 288 (Polychromatic418967fa.accept_13_4_11_2_1_1458 69 206 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 206 288 2 34 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 206 288 (accept_3_4 67 206 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 206 288 2 33 103 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 206 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 206 288 2 32 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 206 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 206 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 206 288 2 31 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 206 288 (accept_3_4 61 206 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 206 288 2 30 103 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 206 288
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 59 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 206 288 2 29 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 206 288 (Polychromatic418967fa.accept_22_13_8_2_1_8451 57 206 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 206 288 2 28 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 206 288 (accept_3_4 55 206 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 206 288 2 27 103 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 206 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 206 288 2 26 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 206 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 206 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 206 288 2 25 103 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 206 288 (accept_3_4 49 206 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 206 288 2 24 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 206 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 47
  206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 206 288 2 23 103 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 206 288
  (Polychromatic418967fa.accept_21_3_17_15_1_4199 45 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 206 288 2 22 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 206 288 (accept_3_4 43 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 206 288 2 21 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 206 288 (Polychromatic418967fa.accept_34_7_2_16_1_17832 41 206 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 206 288 2 20 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 206 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 206 288 2 19 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 206 288 (accept_3_4 37 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 206 288 2 18 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 206 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 206 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 206 288 2 17 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 206 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 206 288 2 16 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 206 288 (accept_3_4 31 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 206 288 2 15 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 206 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 206 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 206 288 2 14 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 206 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 206 288 2 13 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 206 288 (accept_3_4 25 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 206 288 2 12 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 206 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 206 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 206 288 2 11 103 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 206 288
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 206 288 2 10 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 206 288 (accept_3_4 19 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 206 288 2 9 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 206 288 (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 206 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 288 2 8 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 288
  (Polychromatic418967fa.accept_19_15_16_3_1_8409 15 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 206 288 2 7 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 206 288 (accept_3_4 13 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 288 2 6 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 206 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 288 2 5 103 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 288 2 4 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 288 (accept_3_4 7 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 288 2 3 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 206 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 288 2 2 103 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 288 2 1 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 288 (accept_3_4 1 206 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 205 288 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 205 288 (accept_3_5 83 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 205 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 82 205 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 205 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 81 205
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 205 288 (accept_3_5 80 205
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 205 288
  (Polychromatic418967fa.accept_22_13_7_2_1_17712 79 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 205 288 (Polychromatic418967fa.accept_23_9_21_12_1_17761 78 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 205 288 (accept_3_5 77 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 205 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 205 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 205 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 75 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 205 288 (accept_3_5 74 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 205 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 205 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 205 288 (accept_3_5 71 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 205 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 70 205
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 205 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 205 288 (accept_3_5 68 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 205 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 67 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 205 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 205 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 205 288 (accept_3_5 65 205 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 205 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 205 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 205 288 (accept_3_5 62 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 205 288 (Polychromatic418967fa.accept_22_17_7_2_1_11696 61 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 205 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 60 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 205 288 (accept_3_5 59 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 205 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 58 205
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 205 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 57 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 205 288 (accept_3_5 56 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 205 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 205 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 54 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 205 288 (accept_3_5 53 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 205 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 205 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 205 288
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 51 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 205 288 (accept_3_5 50 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 205 288 (Polychromatic418967fa.accept_17_15_1_16_1_8166 49 205 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 205 288 (Polychromatic418967fa.accept_7_6_2_1_1_214
  48 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 205 288 (accept_3_5 47
  205 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 205 288
  (Polychromatic418967fa.accept_17_12_1_16_1_4360 46 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 205 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 205 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 205 288 (accept_3_5 44 205 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 205 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 205 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 205 288 (accept_3_5 41 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 205 288 (Polychromatic418967fa.accept_22_18_7_2_1_10017 40 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 205 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 39 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 205 288 (accept_3_5 38 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 205 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 205
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 205 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 205 288 (accept_3_5 35 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 205 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 205 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 205 288 (accept_3_5 32 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 205 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 205 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 205 288
  (Polychromatic418967fa.accept_20_10_5_8_1_6385 30 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 205 288 (accept_3_5 29 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 205 288 (Polychromatic418967fa.accept_15_13_10_3_1_1952 28 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 205 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 205 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 288 (accept_3_5 26 205 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 25 205 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 205 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 205 288 (accept_3_5 23 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 205 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 205 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 205 288 (accept_3_5 20 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 205 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 19 205
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 288
  (Polychromatic418967fa.accept_13_5_10_2_1_856 18 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 205 288 (accept_3_5 17 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 205 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 16 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 205 288 (Polychromatic418967fa.accept_14_1_9_8_1_2863 15 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 205 288 (accept_3_5 14 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 205 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 205 288 (accept_3_5 11 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 205 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 205 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 205 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 288 (accept_3_5 8 205 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 205 288 (accept_3_5 5 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  205 288 (Polychromatic418967fa.accept_28_4_9_8_1_17831 4 205 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 205 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 205 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 288 (accept_3_5 2 205 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 288 (Polychromatic418967fa.accept_14_1_9_8_1_2863 1 205 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 204 288
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 204 288 12 7 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 204 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 83 204
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 204 288 2 41 102 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 204 288 3 27 68 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 204 288 4 20 51
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 204 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 79 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 204 288 6 13 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 204 288 (Polychromatic418967fa.accept_22_11_6_2_1_16240 77 204 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 204 288 4 19 51 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 204 288 3 25 68 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 204 288 2 37 102 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 204 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 73 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 204 288 12 6 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 204 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 71 204 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 204 288 2 35 102 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 204 288 3 23 68 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 204 288 4 17 51 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 204 288
  (Polychromatic418967fa.accept_22_1_6_2_1_8444 67 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 204 288 6 11 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 204 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 65 204 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 204 288 4 16 51 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 204 288 3 21 68 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 204 288 2 31 102 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 204 288
  (Polychromatic418967fa.accept_22_17_6_2_1_14733 61 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 204 288 12 5 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 204 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 204 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 204 288 2 29 102 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 204 288 3 19 68 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 204 288 4 14 51 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 204 288
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 55 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 204 288 6 9 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 204 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 53 204 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 204 288 4 13 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 204 288 3 17 68 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 204 288 2 25 102 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 204 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 204 288 12 4 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 204 288 (Polychromatic418967fa.accept_19_9_14_3_1_2912 47 204 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 204 288 2 23 102 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 204 288 3 15 68 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 204 288 4 11 51 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 204 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 43 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 204 288 6 7 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 204 288 (Polychromatic418967fa.accept_22_19_6_2_1_16233 41 204 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 204 288 4 10 51 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 204 288 3 13 68 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 204 288 2 19 102 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 204 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 37 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 204 288 12 3 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 204 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 35 204 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 204 288 2 17 102 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 204 288 3 11 68 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 204 288 4 8 51 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 288
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 204 288 6 5 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 204 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 204 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 204 288 4 7 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 204 288 3 9 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 204 288 2 13 102 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 204 288
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 204 288 12 2 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 204 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 204 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 288 2 11 102 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 204 288 3 7 68 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 204 288 4 5 51 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 204 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 204 288 6 3 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 204 288 (Polychromatic418967fa.accept_19_17_14_3_1_5572 17 204 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 288 4 4 51 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 204 288 3 5 68 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 204 288 2 7 102 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 288 12 1 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 204 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 204 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 204 288 2 5 102 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 204 288 3 3 68 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 204 288 4 2 51 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 288
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 288 6 1 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 204 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 204 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 288 4 1 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 204 288 3 1 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 204 288 2 1 102 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1
  204 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 203 288
  (Eq.refl Bool.true) (allA_succ_of_accept 85 203 288 (accept_3_4 85 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 203 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 84 203 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 203 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 83 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 203 288 (accept_3_4 82 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 203 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 81 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 203 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 80 203 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 203 288 (accept_3_4 79 203 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 203 288 (Polychromatic418967fa.accept_20_18_3_8_1_7903 78 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 203 288
  (Polychromatic418967fa.accept_22_11_5_2_1_3658 77 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 203 288 (accept_3_4 76 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 203 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 75 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 203 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 74 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 203 288 (accept_3_4 73 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 203 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 72 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 203 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 71 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 203 288 (accept_3_4 70 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 203 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 69 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 203 288 (Polychromatic418967fa.accept_19_11_13_3_1_9820 68 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 203 288 (accept_3_4 67 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 203 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 66 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 203 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 65 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 203 288 (accept_3_4 64 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 203 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 203 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 62 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 203 288 (accept_3_4 61 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 203 288 (Polychromatic418967fa.accept_21_18_14_15_1_5809 60
  203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 203 288
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 59 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 203 288 (accept_3_4 58 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 203 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 57 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 203 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 203 288 (accept_3_4 55 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 203 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 54 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 203 288
  (Polychromatic418967fa.accept_20_13_3_8_1_4865 53 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 203 288 (accept_3_4 52 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 203 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 203 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 50 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 203 288 (accept_3_4 49 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 203 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 48 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 203 288
  (Polychromatic418967fa.accept_19_9_13_3_1_9829 47 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 203 288 (accept_3_4 46 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 203 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 203 288 (Polychromatic418967fa.accept_23_21_19_12_1_14593 44 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 203 288 (accept_3_4 43 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 203 288 (Polychromatic418967fa.accept_15_12_8_3_1_1995 42 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 203 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 41 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 203 288 (accept_3_4 40 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 203 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 39 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 203 288 (Polychromatic418967fa.accept_20_18_3_8_1_7903 38 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 203 288 (accept_3_4 37 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 203 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 203 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 203 288 (accept_3_4 34 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 203 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 203 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 32 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 288 (accept_3_4 31 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 288
  (Polychromatic418967fa.accept_14_1_7_8_1_2063 29 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 203 288 (accept_3_4 28 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 203 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 27 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 203 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 288 (accept_3_4 25 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 288
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 203 288 (accept_3_4 22 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 203 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 203 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 288 (accept_3_4 19 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 288 (Polychromatic418967fa.accept_20_18_3_8_1_7903 18 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 288
  (Polychromatic418967fa.accept_21_17_14_15_1_5750 17 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 203 288 (accept_3_4 16 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 203 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 203 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 203 288 (Polychromatic418967fa.accept_20_14_3_8_1_4914 14 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 288 (accept_3_4 13 203
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 288
  (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 203 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 203 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 288 (accept_3_4 10 203 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 203 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 203 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629
  8 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 288 (accept_3_4 7
  203 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 203 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 203 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 288 (accept_3_4 4 203 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 203 288 (Polychromatic418967fa.accept_21_3_14_15_1_10526 3 203 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 288
  (Polychromatic418967fa.accept_31_2_17_9_1_17830 2 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 288 (accept_3_4 1 203 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 202 288
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 202 288 2 43 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 202 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 85 202 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 202 288 2 42 101 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 202 288 (accept_3_5 83
  202 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 202 288 2 41 101 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 202 288
  (Polychromatic418967fa.accept_21_18_13_15_1_2884 81 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 202 288 2 40 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 202 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 202 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 202 288 2 39 101 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 202 288 (accept_3_5 77 202 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 202 288 2 38 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 202 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 202 288 2 37 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 202 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 73 202 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 202 288 2 36 101 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 202 288 (accept_3_5 71 202 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 202 288 2 35 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 202 288
  (Polychromatic418967fa.accept_17_1_15_16_1_2202 69 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 202 288 2 34 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 202 288 (Polychromatic418967fa.accept_19_10_12_3_1_12558 67 202 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 202 288 2 33 101 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 202 288 (accept_3_5 65
  202 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 202 288 2 32 101 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 202 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 63 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 202 288 2 31 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 202 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 202 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 202 288 2 30 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 202 288 (accept_3_5 59 202 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 202 288 2 29 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 202 288 (Polychromatic418967fa.accept_13_5_7_2_1_852
  57 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 202 288 2 28 101 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 202 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 55 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 202 288 2 27 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 202 288 (accept_3_5 53 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 202 288 2 26 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 202 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 202 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 202 288 2 25 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 202 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 49 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 202 288 2 24 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 202 288 (accept_3_5 47 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 202 288 2 23 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 202 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 202 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 202 288 2 22 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 202 288
  (Polychromatic418967fa.accept_22_21_4_2_1_8487 43 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 202 288 2 21 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 202 288 (accept_3_5 41 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 202 288 2 20 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 202 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 39 202 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 202 288 2 19 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 202 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 202 288 2 18 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 202 288 (accept_3_5 35 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 202 288 2 17 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 202 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 202 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 202 288 2 16 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 202 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 31 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 202 288 2 15 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 202 288 (accept_3_5 29 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 202 288 2 14 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 202 288 (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 202 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 202 288 2 13 101 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 202 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 202 288 2 12 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 202 288 (accept_3_5 23 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 202 288 2 11 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 202 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 202 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 202 288 2 10 101 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 202 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 202 288 2 9 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 202 288 (accept_3_5 17 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 202 288 2 8 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 202 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 202 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 202 288 2 7 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 288
  (Polychromatic418967fa.accept_19_13_12_3_1_5540 13 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 202 288 2 6 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 202 288 (accept_3_5 11 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 288 2 5 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 202 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 288 2 4 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 7 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 288 2 3 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 288 (accept_3_5 5 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 288 2 2 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 288 (Polychromatic418967fa.accept_27_3_13_18_1_10346 3 202 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 288 2 1 101 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 288
  (Polychromatic418967fa.accept_17_1_15_16_1_2202 1 202 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  88 201 288 (Eq.refl Bool.true) (allA_succ_of_gcd 87 201 288 3 29 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 201 288 (Polychromatic418967fa.accept_13_8_6_2_1_865
  86 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 201 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 85 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 201 288 3 28 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 201 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 201 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 201 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437
  82 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 201 288 3 27 67 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 201 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 80 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 201 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 79 201 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 201 288 3 26 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 201 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441
  77 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 201 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 76 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 201 288 3 25 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 201 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 74 201 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 201 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 73
  201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 201 288 3 24 67 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 201 288
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 71 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 201 288 (Polychromatic418967fa.accept_15_10_6_3_1_1160 70 201 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 201 288 3 23 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 201 288
  (Polychromatic418967fa.accept_21_5_12_15_1_11875 68 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 201 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 201 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 201 288 3 22 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 201 288
  (Polychromatic418967fa.accept_15_5_6_3_1_525 65 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 201 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 64 201 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 201 288 3 21 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 201 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 62
  201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 201 288
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 61 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 201 288 3 20 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 201 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 201 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 201 288
  (Polychromatic418967fa.accept_19_1_11_3_1_5463 58 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 201 288 3 19 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 201 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 56 201 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 201 288 3 18 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 201 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 201 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 52
  201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 201 288 3 17 67 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 201 288
  (Polychromatic418967fa.accept_15_5_6_3_1_525 50 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 201 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 201 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 201 288 3 16 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 201 288 (Polychromatic418967fa.accept_13_8_6_2_1_865
  47 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 46 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 201 288 3 15 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 201 288 (Polychromatic418967fa.accept_27_17_12_18_1_17829 44 201 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 43 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 201 288 3 14 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 201 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 201 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 288 (Polychromatic418967fa.accept_13_1_6_2_1_377
  40 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 201 288 3 13 67 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 201 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 201 288 (Polychromatic418967fa.accept_19_18_11_3_1_11183 37 201 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 201 288 3 12 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 201 288
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 201 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 201 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 201 288 3 11 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 201 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 32
  201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 201 288 3 10 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 201 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 201 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 288
  (Polychromatic418967fa.accept_17_11_14_16_1_1270 28 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 201 288 3 9 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 201 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 201 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 201 288 3 8 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 201 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 201 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 22 201
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 201 288 3 7 67 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 201 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 201 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 201 288 3 6 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 201 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 17
  201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 288
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 201 288 3 5 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 201 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 14 201 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 201 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 201 288 3 4 67 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 201 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 201 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 201 288 3 3 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 201 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 201 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 288
  (Polychromatic418967fa.accept_20_7_1_8_1_10806 7 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 201 288 3 2 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 201 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 201 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 201 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 201 288 3 1 67 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 201 288
  (Polychromatic418967fa.accept_17_2_14_16_1_2187 2 201 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 201 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 201
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 200 288
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 200 288 8 11 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 200 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 200 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 200 288 2 43 100 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 200 288 (accept_3_4 85
  200 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 200 288 4 21 50 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 200 288
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 83 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 200 288 2 41 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 200 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 81 200 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 200 288 8 10 25 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 200 288 (accept_3_4 79 200 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 200 288 2 39 100 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 200 288
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 77 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 200 288 4 19 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 200 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 200 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 200 288 2 37 100 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 200 288 (accept_3_4 73 200 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 200 288 8 9 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 200 288
  (Polychromatic418967fa.accept_17_3_13_16_1_2183 71 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 200 288 2 35 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 200 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 69 200 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 200 288 4 17 50 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 200 288 (accept_3_4 67 200 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 200 288 2 33 100 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 200 288
  (Polychromatic418967fa.accept_23_19_16_12_1_17828 65 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 200 288 8 8 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 200 288 (Polychromatic418967fa.accept_17_12_13_16_1_3226 63 200 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 200 288 2 31 100 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 200 288 (accept_3_4 61
  200 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 200 288 4 15 50 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 200 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 200 288 2 29 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 200 288 (Polychromatic418967fa.accept_27_3_11_18_1_17827 57 200 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 200 288 8 7 25 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 200 288 (accept_3_4 55 200 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 200 288 2 27 100 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 200 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 53 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 200 288 4 13 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 200 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 51 200 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 200 288 2 25 100 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 200 288 (accept_3_4 49 200 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 200 288 8 6 25 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 200 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 200 288 2 23 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 200 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 200 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 200 288 4 11 50 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 200 288 (accept_3_4 43 200 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 200 288 2 21 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 200 288
  (Polychromatic418967fa.accept_27_14_11_18_1_17709 41 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 200 288 8 5 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 200 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 39 200 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 200 288 2 19 100 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 200 288 (accept_3_4 37 200 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 200 288 4 9 50 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 200 288
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 200 288 2 17 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 200 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 200 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 200 288 8 4 25 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 200 288 (accept_3_4 31 200 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 200 288 2 15 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 200 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475
  29 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 200 288 4 7 50 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 200 288
  (Polychromatic418967fa.accept_21_6_11_15_1_13454 27 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 200 288 2 13 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 200 288 (accept_3_4 25 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 200 288 8 3 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 200 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 200 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 200 288 2 11 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 200 288 (Polychromatic418967fa.accept_15_6_5_3_1_1988
  21 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 200 288 4 5 50 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 200 288
  (accept_3_4 19 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 200 288 2 9 100 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 200 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 200 288 8 2 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 200 288 (Polychromatic418967fa.accept_19_15_10_3_1_12550 15 200 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 200 288 2 7 100 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 200 288 (accept_3_4 13 200 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 200 288 4 3 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 200 288 (Polychromatic418967fa.accept_14_11_4_8_1_664
  11 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 288 2 5 100 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 288
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 200 288 8 1 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 200 288 (accept_3_4 7 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200
  288 2 3 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  200 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 200 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 200 288 4 1 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 200 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 200 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 200 288 2 1 100 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 200 288 (accept_3_4 1 200 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 200
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 199 288
  (Eq.refl Bool.true) (allA_succ_of_accept 89 199 288 (accept_3_5 89 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 199 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 88 199 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 199 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 87 199
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 199 288 (accept_3_5 86 199
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 199 288
  (Polychromatic418967fa.accept_21_1_10_15_1_2828 85 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 199 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 199 288 (accept_3_5 83 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 199 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 82 199 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 199 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 199 288 (accept_3_5 80 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 199 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 199 288 (Polychromatic418967fa.accept_22_12_1_2_1_13238 78 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 199 288 (accept_3_5 77 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 199 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 76 199
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 199 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 199 288 (accept_3_5 74 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 199 288 (Polychromatic418967fa.accept_22_7_1_2_1_17757 73 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 199 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 199 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 199 288 (accept_3_5 71 199 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 199 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 70 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 199 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 69 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 199 288 (accept_3_5 68 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 199 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 199 288 (Polychromatic418967fa.accept_21_3_10_15_1_4266 66 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 199 288 (accept_3_5 65 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 199 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 64 199
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 199 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 63 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 199 288 (accept_3_5 62 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 199 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 199 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 199 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 199 288 (accept_3_5 59 199 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 199 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 199 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 199 288 (accept_3_5 56 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 199 288 (Polychromatic418967fa.accept_27_1_10_18_1_17826 55 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 199 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 199 288 (accept_3_5 53 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 199 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 52 199
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 199 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 199 288 (accept_3_5 50 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 199 288 (Polychromatic418967fa.accept_19_11_9_3_1_4167 49 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 199 288 (Polychromatic418967fa.accept_19_10_9_3_1_7009 48 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 199 288 (accept_3_5 47 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 199 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 199 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 199 288
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 199 288 (accept_3_5 44 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 199 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 199 288 (Polychromatic418967fa.accept_25_17_24_13_1_17825 42 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 199 288 (accept_3_5 41 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 199 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 199 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 199 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 199 288 (accept_3_5 38 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 199 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 199 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 199 288 (accept_3_5 35 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 199 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 199
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 199 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 199 288 (accept_3_5 32 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 199 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 199 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 199 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 199 288 (accept_3_5 29 199 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 199 288 (Polychromatic418967fa.accept_17_11_12_16_1_3219 28 199 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 199 288 (accept_3_5 26 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 199 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 199 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 199 288 (accept_3_5 23 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 199 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 22 199
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 21 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 199 288 (accept_3_5 20 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 199 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 199 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 199 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 288 (accept_3_5 17 199 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 199 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 288
  (Polychromatic418967fa.accept_19_15_9_3_1_13764 15 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 199 288 (accept_3_5 14 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 199 288 (Polychromatic418967fa.accept_17_13_12_16_1_6908 13 199 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 288 (Polychromatic418967fa.accept_7_5_3_1_1_424
  12 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 288 (accept_3_5 11
  199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 199 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 199 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 288 (accept_3_5 8 199 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 199 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 199 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433
  6 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 288 (accept_3_5 5
  199 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 199 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 199 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 199 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 288 (accept_3_5 2 199 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 199 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 199 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 198 288
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 198 288 18 5 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 198 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 89 198
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 198 288 2 44 99 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 198 288 3 29 66 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 198 288 2 43 99
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 198 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 85 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 198 288 6 14 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 198 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 198 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 198 288 2 41 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 198 288 9 9 22 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 198 288 2 40 99 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 198 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 79 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 198 288 6 13 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 198 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 77 198 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 198 288 2 38 99 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 198 288 3 25 66 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 198 288 2 37 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 198 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 198 288 18 4 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 198 288 (Polychromatic418967fa.accept_14_1_2_8_1_655 71 198 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 198 288 2 35 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 198 288 3 23 66 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 198 288 2 34 99 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 198 288
  (Polychromatic418967fa.accept_21_4_9_15_1_11925 67 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 198 288 6 11 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 198 288 (Polychromatic418967fa.accept_17_14_11_16_1_3261 65 198 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 198 288 2 32 99 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 198 288 9 7 22 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 198 288 2 31 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 198 288
  (Polychromatic418967fa.accept_13_9_3_2_1_399 61 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 198 288 6 10 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 198 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 198 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 198 288 2 29 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 198 288 3 19 66 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 198 288 2 28 99 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 198 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 55 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 198 288 18 3 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 198 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 53 198 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 198 288 2 26 99 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 198 288 3 17 66 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 198 288 2 25 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 198 288
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 49 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 198 288 6 8 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 198 288 (Polychromatic418967fa.accept_21_5_9_15_1_11924 47 198 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 198 288 2 23 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 198 288 9 5 22 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 198 288 2 22 99 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 198 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 43 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 198 288 6 7 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 198 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 198 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 198 288 2 20 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 198 288 3 13 66 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 198 288 2 19 99 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 198 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 37 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 288 18 2 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 198 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 35 198 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 288 2 17 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 198 288 3 11 66 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 198 288 2 16 99 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 198 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 288 6 5 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 198 288 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 198 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 288 2 14 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 198 288 9 3 22 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 198 288 2 13 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 288
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 25 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 288 6 4 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 198 288 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 198 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 288 2 11 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 198 288 3 7 66 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 198 288 2 10 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 288
  (Polychromatic418967fa.accept_21_19_9_15_1_4217 19 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 198 288 18 1 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 198 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 198 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 288 2 8 99 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 198 288 3 5 66 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 198 288 2 7 99 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 288 6 2 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 198 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 198 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 288 2 5 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 198 288 9 1 22 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 198 288 2 4 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 288 (Polychromatic418967fa.accept_21_7_9_15_1_5803
  7 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 288 6 1 33 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 288
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 5 198 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 198 288 2 2 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 198 288 3 1 66 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 198 288 2 1 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 198 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 198 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 198
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 197 288
  (Eq.refl Bool.true) (allA_succ_of_accept 91 197 288 (accept_3_4 91 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 197 288 (Polychromatic418967fa.accept_19_14_7_3_1_5491 90 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 197 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 89 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 197 288 (accept_3_4 88 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 197 288
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 87 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 197 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 86 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 197 288 (accept_3_4 85 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 197 288 (Polychromatic418967fa.accept_25_9_22_13_1_17824 84 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 197 288
  (Polychromatic418967fa.accept_25_8_22_13_1_17750 83 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 197 288 (accept_3_4 82 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 197 288 (Polychromatic418967fa.accept_19_5_7_3_1_6990 81 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 197 288 (Polychromatic418967fa.accept_15_5_2_3_1_4876 80 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 197 288 (accept_3_4 79 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 197 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 78 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 197 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873 77 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 197 288 (accept_3_4 76 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 197 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 75 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 197 288
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 74 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 197 288 (accept_3_4 73 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 197 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 72 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 197 288 (Polychromatic418967fa.accept_19_14_7_3_1_5491 71 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 197 288 (accept_3_4 70 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 197 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 197 288
  (Polychromatic418967fa.accept_21_5_8_15_1_11890 68 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 197 288 (accept_3_4 67 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 197 288 (Polychromatic418967fa.accept_21_3_8_15_1_4301 66 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 197 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 197 288 (accept_3_4 64 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 197 288
  (Polychromatic418967fa.accept_14_7_1_8_1_2873 63 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 197 288 (Polychromatic418967fa.accept_19_5_7_3_1_6990 62 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 197 288 (accept_3_4 61 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 197 288 (Polychromatic418967fa.accept_17_9_10_16_1_3217 60 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 197 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 59 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 197 288 (accept_3_4 58 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 197 288 (Polychromatic418967fa.accept_15_12_2_3_1_1146 57 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 197 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 56 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 197 288 (accept_3_4 55 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 197 288 (Polychromatic418967fa.accept_21_12_8_15_1_8955 54 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 197 288
  (Polychromatic418967fa.accept_19_15_7_3_1_4143 53 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 197 288 (accept_3_4 52 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 197 288 (Polychromatic418967fa.accept_14_9_1_8_1_2849 51 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 197 288 (Polychromatic418967fa.accept_15_5_2_3_1_4876 50 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 197 288 (accept_3_4 49 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 197 288 (Polychromatic418967fa.accept_19_10_7_3_1_6977 48 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 197 288
  (Polychromatic418967fa.accept_20_7_17_8_1_3452 47 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 197 288 (accept_3_4 46 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 197 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 197 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 44 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 197 288 (accept_3_4 43 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 197 288 (Polychromatic418967fa.accept_15_12_2_3_1_1146 42 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 197 288
  (Polychromatic418967fa.accept_17_7_10_16_1_5582 41 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 197 288 (accept_3_4 40 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 197 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 288 (Polychromatic418967fa.accept_21_17_8_15_1_10549 38
  197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 197 288 (accept_3_4 37
  197 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 197 288
  (Polychromatic418967fa.accept_22_14_21_2_1_14717 36 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 197 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 288 (accept_3_4 34 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 288 (Polychromatic418967fa.accept_19_14_7_3_1_5491 33 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 288
  (Polychromatic418967fa.accept_19_13_7_3_1_9798 32 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 288 (accept_3_4 31 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 30 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 288 (accept_3_4 28 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 288 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 288
  (Polychromatic418967fa.accept_17_9_10_16_1_3217 26 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 197 288 (accept_3_4 25 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 197 288 (Polychromatic418967fa.accept_17_7_10_16_1_5582 24 197 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 288 (Polychromatic418967fa.accept_11_1_10_2_1_58
  23 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 288 (accept_3_4 22
  197 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 288
  (Polychromatic418967fa.accept_14_7_1_8_1_2873 21 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 197 288 (Polychromatic418967fa.accept_15_5_2_3_1_4876 20 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 288 (accept_3_4 19 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 197 288 (Polychromatic418967fa.accept_21_18_8_15_1_5745 18 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 288
  (Polychromatic418967fa.accept_21_17_8_15_1_10549 17 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 197 288 (accept_3_4 16 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 197 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 197 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 288 (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 288 (accept_3_4 13 197
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 197 288 (Polychromatic418967fa.accept_20_11_17_8_1_4903 11 197 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 288 (accept_3_4 10 197 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 288
  (Polychromatic418967fa.accept_22_8_21_2_1_8460 8 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 288 (accept_3_4 7 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 288 (Polychromatic418967fa.accept_17_6_10_16_1_9453 6 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 197 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 288 (accept_3_4 4 197 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 288 (Polychromatic418967fa.accept_21_3_8_15_1_4301 3 197 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 288
  (Polychromatic418967fa.accept_14_2_1_8_1_650 2 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 288 (accept_3_4 1 197 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 196 288
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 196 288 4 23 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 196 288 (Polychromatic418967fa.accept_17_6_9_16_1_4410 91 196
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 196 288 2 45 98 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 196 288 (accept_3_5 89
  196 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 196 288 4 22 49 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 196 288
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 87 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 196 288 2 43 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 196 288 (Polychromatic418967fa.accept_19_9_6_3_1_5563 85 196 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 196 288 4 21 49 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 196 288 (accept_3_5 83 196 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 196 288 2 41 98 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 196 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 81 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 196 288 4 20 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 196 288 (Polychromatic418967fa.accept_15_4_1_3_1_1922 79 196 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 196 288 2 39 98 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 196 288 (accept_3_5 77 196 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 196 288 4 19 49 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 196 288
  (Polychromatic418967fa.accept_19_18_6_3_1_8405 75 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 196 288 2 37 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 196 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 73 196 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 196 288 4 18 49 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 196 288 (accept_3_5 71 196 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 196 288 2 35 98 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 196 288
  (Polychromatic418967fa.accept_22_3_20_2_1_5223 69 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 196 288 4 17 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 196 288 (Polychromatic418967fa.accept_25_17_21_13_1_9067 67 196 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 196 288 2 33 98 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 196 288 (accept_3_5 65 196 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 196 288 4 16 49 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 196 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 196 288 2 31 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 196 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 61 196 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 196 288 4 15 49 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 196 288 (accept_3_5 59 196 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 196 288 2 29 98 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 196 288
  (Polychromatic418967fa.accept_17_6_9_16_1_4410 57 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 196 288 4 14 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 196 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 55 196 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 196 288 2 27 98 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 196 288 (accept_3_5 53 196 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 196 288 4 13 49 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 196 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 51 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 196 288 2 25 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 196 288 (Polychromatic418967fa.accept_15_4_1_3_1_1922 49 196 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 196 288 4 12 49 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 196 288 (accept_3_5 47 196 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 196 288 2 23 98 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 196 288
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 45 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 196 288 4 11 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 196 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 196 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 196 288 2 21 98 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 196 288 (accept_3_5 41 196 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 196 288 4 10 49 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 196 288
  (Polychromatic418967fa.accept_19_1_6_3_1_6968 39 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 196 288 2 19 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 196 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 37 196 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 196 288 4 9 49 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 196 288 (accept_3_5 35 196 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 196 288 2 17 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 196 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169
  33 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 196 288 4 8 49 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 196 288
  (Polychromatic418967fa.accept_21_10_7_15_1_8930 31 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 196 288 2 15 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 196 288 (accept_3_5 29 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 196 288 4 7 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 196 288 (Polychromatic418967fa.accept_17_10_9_16_1_5607 27 196 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 196 288 2 13 98 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 196 288
  (Polychromatic418967fa.accept_13_12_1_2_1_845 25 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 196 288 4 6 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 196 288 (accept_3_5 23 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  196 288 2 11 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 196 288 (Polychromatic418967fa.accept_15_6_1_3_1_2852 21 196 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 196 288 4 5 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 196 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464
  19 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 196 288 2 9 98 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 196 288
  (accept_3_5 17 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 196 288 4 4 49 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 196 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 15 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 196 288 2 7 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 196 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 196 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 196 288 4 3 49 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 196 288 (accept_3_5 11 196 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 196 288 2 5 98 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 196 288
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 196 288 4 2 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 196 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 196 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 196 288 2 3 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 196 288 (accept_3_5 5 196 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196 288 4 1 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 196 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 196 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 196 288 2 1 98 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 196 288
  (Polychromatic418967fa.accept_19_1_6_3_1_6968 1 196 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 196 288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 94 195 288 (Eq.refl Bool.true) (allA_succ_of_gcd 93 195 288 3 31 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 195 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 92 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 195 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 91 195 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 195 288 3 30 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 195 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 89
  195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 195 288
  (Polychromatic418967fa.accept_21_4_6_15_1_5744 88 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 195 288 3 29 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 195 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 86 195 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 195 288
  (Polychromatic418967fa.accept_20_5_15_8_1_4930 85 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 195 288 3 28 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 195 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 83 195 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 195 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 82 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 195 288 3 27 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 195 288 (Polychromatic418967fa.accept_21_17_6_15_1_5765 80 195 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 195 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 79 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 195 288 3 26 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 195 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 77 195 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 195 288
  (Polychromatic418967fa.accept_21_13_6_15_1_5818 76 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 195 288 3 25 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 195 288 (Polychromatic418967fa.accept_19_17_5_3_1_5455 74 195 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 195 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 73 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 195 288 3 24 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 195 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 71 195 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 195 288
  (Polychromatic418967fa.accept_17_2_8_16_1_4403 70 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 195 288 3 23 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 195 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 195 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 195 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167
  67 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 195 288 3 22 65 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 195 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 195 288 (Polychromatic418967fa.accept_19_7_5_3_1_13861 64 195 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 195 288 3 21 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 195 288 (Polychromatic418967fa.accept_10_2_5_8_1_139
  62 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 195 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 195 288 3 20 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 195 288 (Polychromatic418967fa.accept_19_2_5_3_1_5536 59 195 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 195 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 58 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 195 288 3 19 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 195 288 (Polychromatic418967fa.accept_22_12_19_2_1_11680 56 195 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 195 288
  (Polychromatic418967fa.accept_19_17_5_3_1_5455 55 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 195 288 3 18 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 195 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 195 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 195 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 52 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 195 288 3 17 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 195 288 (Polychromatic418967fa.accept_20_10_15_8_1_4818 50 195 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 195 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 49 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 195 288 3 16 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 195 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 195 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 288 (Polychromatic418967fa.accept_19_8_5_3_1_4181
  46 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 195 288 3 15 65 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 195 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 195 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 195 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 195 288 3 14 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 195 288 (Polychromatic418967fa.accept_17_7_8_16_1_6966
  41 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 195 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 40 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 195 288 3 13 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 195 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 38 195 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 37
  195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 195 288 3 12 65 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 195 288
  (Polychromatic418967fa.accept_14_7_13_8_1_2067 35 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 195 288 (Polychromatic418967fa.accept_20_14_15_8_1_9380 34 195 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 195 288 3 11 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 195 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 195 288 (Polychromatic418967fa.accept_17_14_8_16_1_6863 31 195 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 195 288 3 10 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 195 288
  (Polychromatic418967fa.accept_19_10_5_3_1_13818 29 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 195 288 (Polychromatic418967fa.accept_22_6_19_2_1_6814 28 195 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 195 288 3 9 65 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 195 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 195 288 (Polychromatic418967fa.accept_19_6_5_3_1_11210 25 195 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 195 288 3 8 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 195 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 23
  195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 22 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 195 288 3 7 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 195 288 (Polychromatic418967fa.accept_19_1_5_3_1_6970 20 195 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 195 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 195 288 3 6 65 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 195 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 195 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 195 288 3 5 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 195 288
  (Polychromatic418967fa.accept_17_14_8_16_1_6863 14 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 195 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 195 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 195 288 3 4 65 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 195 288
  (Polychromatic418967fa.accept_21_11_6_15_1_5764 11 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 195 288 (Polychromatic418967fa.accept_19_10_5_3_1_13818 10 195 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 195 288 3 3 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 195 288
  (Polychromatic418967fa.accept_19_8_5_3_1_4181 8 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 195 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 195 288 3 2 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 195 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 195 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 288
  (Polychromatic418967fa.accept_21_4_6_15_1_5744 4 195 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 195 288 3 1 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 195 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 195 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 288 (Polychromatic418967fa.accept_19_1_5_3_1_6970 1 195 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 194
  288 (Eq.refl Bool.true) (allA_succ_of_gcd 94 194 288 2 47 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 194 288 (Polychromatic418967fa.accept_17_8_7_16_1_9508 93 194
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 194 288 2 46 97 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 194 288 (accept_3_4 91
  194 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 194 288 2 45 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 194 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 89 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 194 288 2 44 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 194 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 194 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 194 288 2 43 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 194 288 (accept_3_4 85 194 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 194 288 2 42 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 194 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 83
  194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 194 288 2 41 97 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 194 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 81 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 194 288 2 40 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 194 288 (accept_3_4 79 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 194 288 2 39 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 194 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 77 194 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 194 288 2 38 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 194 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 75 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 194 288 2 37 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 194 288 (accept_3_4 73 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 194 288 2 36 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 194 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 71 194 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 194 288 2 35 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 194 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 194 288 2 34 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 194 288 (accept_3_4 67 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 194 288 2 33 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 194 288 (Polychromatic418967fa.accept_19_8_4_3_1_5559 65 194 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 194 288 2 32 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 194 288
  (Polychromatic418967fa.accept_19_6_4_3_1_11188 63 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 194 288 2 31 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 194 288 (accept_3_4 61 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 194 288 2 30 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 194 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 194 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 194 288 2 29 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 194 288
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 57 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 194 288 2 28 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 194 288 (accept_3_4 55 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 194 288 2 27 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 194 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 194 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 194 288 2 26 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 194 288
  (Polychromatic418967fa.accept_19_13_4_3_1_2945 51 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 194 288 2 25 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 194 288 (accept_3_4 49 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 194 288 2 24 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 194 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 47 194 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 194 288 2 23 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 194 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 194 288 2 22 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 194 288 (accept_3_4 43 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 194 288 2 21 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 194 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 194 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 194 288 2 20 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 194 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 194 288 2 19 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 194 288 (accept_3_4 37 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 194 288 2 18 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 194 288 (Polychromatic418967fa.accept_19_16_4_3_1_2946 35 194 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 194 288 2 17 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 288
  (Polychromatic418967fa.accept_20_13_14_8_1_4850 33 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 194 288 2 16 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 194 288 (accept_3_4 31 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 288 2 15 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 194 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 288 2 14 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 288 2 13 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 288 (accept_3_4 25 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 288 2 12 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 288 (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 194 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 288 2 11 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 288
  (Polychromatic418967fa.accept_23_21_10_12_1_14591 21 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 194 288 2 10 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 194 288 (accept_3_4 19 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 288 2 9 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 194 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 288 2 8 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 288
  (Polychromatic418967fa.accept_20_15_14_8_1_9344 15 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 194 288 2 7 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 194 288 (accept_3_4 13 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 288 2 6 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 194 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 288 2 5 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 288 2 4 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 288 (accept_3_4 7 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  288 2 3 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 194 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 288 2 2 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 194 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 288 2 1 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 288 (accept_3_4 1 194 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 193
  288 (Eq.refl Bool.true) (allA_succ_of_accept 95 193 288 (accept_3_5 95 193 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 193 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 94 193 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 193 288
  (Polychromatic418967fa.accept_21_9_4_15_1_5801 93 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 193 288 (accept_3_5 92 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 193 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 91 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 193 288 (Polychromatic418967fa.accept_21_6_4_15_1_9005 90 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 193 288 (accept_3_5 89 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 193 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 88 193
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 193 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 87 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 193 288 (accept_3_5 86 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 193 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 85 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 193 288 (Polychromatic418967fa.accept_15_9_13_3_1_535 84 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 193 288 (accept_3_5 83 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 193 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 82 193 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 193 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 81 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 193 288 (accept_3_5 80 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 193 288 (Polychromatic418967fa.accept_27_25_4_18_1_17766 79 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 193 288 (Polychromatic418967fa.accept_17_10_6_16_1_6862 78 193 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 193 288 (accept_3_5 77 193 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 193 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  76 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 193 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 193 288 (accept_3_5 74 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 193 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 193 288 (Polychromatic418967fa.accept_15_12_13_3_1_1915 72 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 193 288 (accept_3_5 71 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 193 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 70 193 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 193 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 69 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 193 288 (accept_3_5 68 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 193 288 (Polychromatic418967fa.accept_22_1_17_2_1_16261 67 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 193 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 193 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 193 288 (accept_3_5 65 193 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 193 288 (Polychromatic418967fa.accept_23_18_9_12_1_17823 64 193 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 193 288
  (Polychromatic418967fa.accept_20_3_13_8_1_12215 63 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 193 288 (accept_3_5 62 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 193 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 193 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 193 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 60 193
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 193 288 (accept_3_5 59 193
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 193 288
  (Polychromatic418967fa.accept_17_7_6_16_1_2195 58 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 193 288 (Polychromatic418967fa.accept_15_12_13_3_1_1915 57 193 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 193 288 (accept_3_5 56 193 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 193 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 55 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 193 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 193 288 (accept_3_5 53 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 193 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 193 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 193 288 (accept_3_5 50 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 193 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 49 193
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 193 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 48 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 193 288 (accept_3_5 47 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 193 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 193 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 193 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 193 288 (accept_3_5 44 193 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 288 (Polychromatic418967fa.accept_13_4_11_2_1_1458 43 193 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 193 288
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 42 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 193 288 (accept_3_5 41 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 193 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 193 288 (Polychromatic418967fa.accept_15_9_13_3_1_535 39 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 288 (accept_3_5 38 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 193 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 193 288 (accept_3_5 35 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 193 288 (Polychromatic418967fa.accept_20_14_13_8_1_4847 34 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 193 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 193 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 288 (accept_3_5 32 193 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 30 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 193 288 (accept_3_5 29 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 193 288 (Polychromatic418967fa.accept_22_6_17_2_1_3518 28 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 193 288 (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 288 (accept_3_5 26 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 193
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 193 288 (accept_3_5 23 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 193 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 22 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 193 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 288 (accept_3_5 20 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 193 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 288
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 288 (accept_3_5 17 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 288 (accept_3_5 14 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 288 (Polychromatic418967fa.accept_26_13_11_2_1_17822 13
  193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 288 (accept_3_5 11 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 288 (accept_3_5 8 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 288 (Polychromatic418967fa.accept_17_7_6_16_1_2195 7 193
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 288 (accept_3_5 5 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 193 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 193 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 288 (accept_3_5 2 193 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 193 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 192
  288 (Eq.refl Bool.true) (allA_succ_of_gcd 96 192 288 96 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 192 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 192 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 192 288 2 47 96 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 192 288 3 31 64 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 192 288 4 23 48
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 192 288
  (Polychromatic418967fa.accept_21_7_3_15_1_5800 91 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 192 288 6 15 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 192 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 192 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 192 288 8 11 24 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 192 288 3 29 64 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 192 288 2 43 96 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 192 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 85 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 192 288 12 7 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 192 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 83 192 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 192 288 2 41 96 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 192 288 3 27 64 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 192 288 16 5 12 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 192 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 79 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 192 288 6 13 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 192 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 77 192 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 192 288 4 19 48 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 192 288 3 25 64 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 192 288 2 37 96 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 192 288
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 73 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 192 288 24 3 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 192 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 71 192 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 192 288 2 35 96 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 192 288 3 23 64 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 192 288 4 17 48 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 192 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 67 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 192 288 6 11 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 192 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 192 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 192 288 32 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 192 288 3 21 64 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 192 288 2 31 96 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 192 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 192 288 12 5 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 192 288 (Polychromatic418967fa.accept_21_17_3_15_1_5762 59 192 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 192 288 2 29 96 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 192 288 3 19 64 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 192 288 8 7 24 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 192 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 55 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 192 288 6 9 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 192 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 192 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 192 288 4 13 48 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 192 288 3 17 64 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 192 288 2 25 96 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 192 288
  (Polychromatic418967fa.accept_19_11_2_3_1_8424 49 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 192 288 48 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 192 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 192 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 192 288 2 23 96 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 192 288 3 15 64 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 192 288 4 11 48 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 192 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 43 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 192 288 6 7 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 192 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 192 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 192 288 8 5 24 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 192 288 3 13 64 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 192 288 2 19 96 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 192 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 288 12 3 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 192 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 192 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 288 2 17 96 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 192 288 3 11 64 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 192 288 32 1 6 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 288
  (Polychromatic418967fa.accept_13_5_10_2_1_856 31 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 192 288 6 5 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 192 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 29 192 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 288 4 7 48 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 192 288 3 9 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 192 288 2 13 96 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 288 24 1 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 192 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 192 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 288 2 11 96 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 192 288 3 7 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 192 288 4 5 48 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 19
  192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 288 6 3 32 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 288 16 1 12 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 192 288 3 5 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 192 288 2 7 96 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 192 288 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 192 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 288 12 1 16 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 192 288 2 5 96 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 192 288 3 3 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 192 288 8 1 24 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 192 288 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 192 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 288 6 1 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5
  192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192 288 4 1 48 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 192 288 3 1 64 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 192 288 2 1 96 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 288
  (Polychromatic418967fa.accept_17_1_5_16_1_5589 1 192 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 192 288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 98 191 288 (Eq.refl Bool.true) (allA_succ_of_accept 97 191 288 (accept_3_4 97 191 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 191 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 96 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 191 288
  (Polychromatic418967fa.accept_22_7_15_2_1_17821 95 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 191 288 (accept_3_4 94 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 191 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 93 191 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 191 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 92 191
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 191 288 (accept_3_4 91 191
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 191 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 90 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 191 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 89 191 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 191 288 (accept_3_4 88 191 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 191 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 191 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 191 288 (Polychromatic418967fa.accept_11_9_4_2_1_600
  86 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 191 288 (accept_3_4 85
  191 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 191 288
  (Polychromatic418967fa.accept_13_6_9_2_1_838 84 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 191 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 191 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 191 288 (accept_3_4 82 191 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 191 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 81 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 191 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 191 288 (accept_3_4 79 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 191 288 (Polychromatic418967fa.accept_19_2_1_3_1_11216 78 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 191 288 (Polychromatic418967fa.accept_20_17_11_8_1_4894 77 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 191 288 (accept_3_4 76 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 191 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 75 191
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 191 288
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 74 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 191 288 (accept_3_4 73 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 191 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 72 191 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 191 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 71 191
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 191 288 (accept_3_4 70 191
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 191 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 191 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 68 191 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 191 288 (accept_3_4 67 191 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 191 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 191 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 191 288
  (Polychromatic418967fa.accept_23_19_7_12_1_16212 65 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 191 288 (accept_3_4 64 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 191 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 63 191 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 191 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 191 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 191 288 (accept_3_4 61 191 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 191 288
  (Polychromatic418967fa.accept_21_18_2_15_1_5737 60 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 191 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 191 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 191 288 (accept_3_4 58 191 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 191 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 57 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 191 288
  (Polychromatic418967fa.accept_17_5_4_16_1_6925 56 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 191 288 (accept_3_4 55 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 191 288 (Polychromatic418967fa.accept_17_3_4_16_1_3208 54 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 191 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 53 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 191 288 (accept_3_4 52 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 191 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 191
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 191 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 50 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 191 288 (accept_3_4 49 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 191 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 191 288 (Polychromatic418967fa.accept_25_22_16_13_1_17768 47 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 191 288 (accept_3_4 46 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 191 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 191 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 191 288
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 44 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 191 288 (accept_3_4 43 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 191 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 42 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 191 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 191 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 191 288 (accept_3_4 40 191 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 191 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 39 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 191 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 191 288 (accept_3_4 37 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 191 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 191 288 (Polychromatic418967fa.accept_19_16_1_3_1_7007 35 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 191 288 (accept_3_4 34 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 191 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 33 191
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 191 288
  (Polychromatic418967fa.accept_13_6_9_2_1_838 32 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 191 288 (accept_3_4 31 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 191 288 (Polychromatic418967fa.accept_19_11_1_3_1_5555 30 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 191 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 191 288 (accept_3_4 28 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 191 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 191 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 191 288
  (Polychromatic418967fa.accept_25_1_16_13_1_3426 26 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 191 288 (accept_3_4 25 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 191 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 191 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 191
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 288 (accept_3_4 22 191
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 191 288
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 191 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 191 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 288 (accept_3_4 19 191 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 191 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 288 (accept_3_4 16 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 288 (Polychromatic418967fa.accept_14_1_9_8_1_2863 15 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 14 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 288 (accept_3_4 13 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 288 (Polychromatic418967fa.accept_27_12_2_18_1_13989 12
  191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 288
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 191 288 (accept_3_4 10 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  191 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 191 288 (Polychromatic418967fa.accept_15_8_11_3_1_3847 8 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 288 (accept_3_4 7 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 191 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 288
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 288 (accept_3_4 4 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 191 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 288 (Polychromatic418967fa.accept_19_2_1_3_1_11216 2 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 288 (accept_3_4 1 191 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 191
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  190 288 (Eq.refl Bool.true) (allA_succ_of_gcd 98 190 288 2 49 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 190 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 97 190
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 190 288 2 48 95 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 190 288 (accept_3_5 95
  190 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 190 288 2 47 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 190 288
  (Polychromatic418967fa.accept_26_15_8_2_1_17820 93 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 190 288 2 46 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 190 288 (Polychromatic418967fa.accept_21_7_1_15_1_680 91 190 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 190 288 2 45 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 190 288 (accept_3_5 89 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 190 288 2 44 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 190 288
  (Polychromatic418967fa.accept_20_7_10_8_1_9411 87 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 190 288 2 43 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 190 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 85 190 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 190 288 2 42 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 190 288 (accept_3_5 83 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 190 288 2 41 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 190 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 81 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 190 288 2 40 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 190 288 (Polychromatic418967fa.accept_21_16_1_15_1_14811 79 190 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 190 288 2 39 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 190 288 (accept_3_5 77 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 190 288 2 38 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 190 288
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 75 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 190 288 2 37 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 190 288 (Polychromatic418967fa.accept_15_13_10_3_1_1952 73 190 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 190 288 2 36 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 190 288 (accept_3_5 71 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 190 288 2 35 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 190 288
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 69 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 190 288 2 34 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 190 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 67 190 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 190 288 2 33 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 190 288 (accept_3_5 65 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 190 288 2 32 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 190 288
  (Polychromatic418967fa.accept_22_19_14_2_1_3635 63 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 190 288 2 31 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 190 288 (Polychromatic418967fa.accept_21_19_1_15_1_11887 61 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 190 288 2 30 95 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 190 288 (accept_3_5 59
  190 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 190 288 2 29 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 190 288
  (Polychromatic418967fa.accept_20_17_10_8_1_9374 57 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 190 288 2 28 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 190 288 (Polychromatic418967fa.accept_17_4_3_16_1_9483 55 190 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 190 288 2 27 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 190 288 (accept_3_5 53 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 190 288 2 26 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 190 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 51 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 190 288 2 25 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 190 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 49 190 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 190 288 2 24 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 190 288 (accept_3_5 47 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 190 288 2 23 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 190 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 190 288 2 22 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 190 288 (Polychromatic418967fa.accept_15_13_10_3_1_1952 43 190 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 190 288 2 21 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 190 288 (accept_3_5 41 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 190 288 2 20 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 190 288
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 39 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 190 288 2 19 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 190 288 (Polychromatic418967fa.accept_15_7_10_3_1_2891 37 190 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 190 288 2 18 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 190 288 (accept_3_5 35 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 190 288 2 17 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 190 288
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 190 288 2 16 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 190 288 (Polychromatic418967fa.accept_21_10_1_15_1_10541 31 190 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 190 288 2 15 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 190 288 (accept_3_5 29 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 190 288 2 14 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 190 288
  (Polychromatic418967fa.accept_20_7_10_8_1_9411 27 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 190 288 2 13 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 190 288 (Polychromatic418967fa.accept_20_5_10_8_1_6397 25 190 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 190 288 2 12 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 190 288 (accept_3_5 23 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 190 288 2 11 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 190 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 190 288 2 10 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 190 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 190 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 190 288 2 9 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 190 288 (accept_3_5 17 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 190 288 2 8 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 190 288
  (Polychromatic418967fa.accept_20_15_10_8_1_6398 15 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 190 288 2 7 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 190 288 (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 190 288 2 6 95 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 190 288 (accept_3_5 11
  190 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 190 288 2 5 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 190 288
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 190 288 2 4 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 190 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 190 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 190 288 2 3 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 190 288 (accept_3_5 5 190 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190 288 2 2 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 190 288 (Polychromatic418967fa.accept_21_3_1_15_1_4287 3 190 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 190 288 2 1 95 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 190 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 190 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 190 288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 100 189 288 (Eq.refl Bool.true) (allA_succ_of_gcd 99 189 288 9 11 21 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 189 288
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 98 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 189 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 97 189 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 189 288 3 32 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 189 288 (Polychromatic418967fa.accept_15_5_9_3_1_528
  95 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 189 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 94 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 189 288 3 31 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 189 288 (Polychromatic418967fa.accept_19_16_18_3_1_15081 92 189 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 189 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 91 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 189 288 9 10 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 189 288 (Polychromatic418967fa.accept_28_5_21_8_1_17819 89 189 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 189 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 88 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 189 288 3 29 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 189 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 86 189 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 189 288
  (Polychromatic418967fa.accept_14_1_7_8_1_2063 85 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 189 288 3 28 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 189 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 83 189 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 189 288
  (Polychromatic418967fa.accept_17_14_2_16_1_4380 82 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 81 189 288 9 9 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 80 189 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 80 189 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 189 288
  (Polychromatic418967fa.accept_20_19_9_8_1_12192 79 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 189 288 3 26 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 189 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 77 189 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 189 288
  (Polychromatic418967fa.accept_14_6_7_8_1_624 76 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 189 288 3 25 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 189 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 74 189 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 189 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988
  73 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 189 288 9 8 21 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 189 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 71 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 189 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 70 189 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 189 288 3 23 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 189 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194
  68 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 189 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 67 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 189 288 3 22 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 189 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 65 189 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 288 (Polychromatic418967fa.accept_10_4_9_8_1_125
  64 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 189 288 9 7 21 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 189 288
  (Polychromatic418967fa.accept_14_6_7_8_1_624 62 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 189 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 61 189 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 189 288 3 20 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 189 288 (Polychromatic418967fa.accept_17_8_2_16_1_5598
  59 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 189 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 58 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 189 288 3 19 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 189 288 (Polychromatic418967fa.accept_17_5_2_16_1_1294 56 189 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 189 288
  (Polychromatic418967fa.accept_14_13_7_8_1_677 55 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 189 288 9 6 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 189 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 53 189 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 288 (Polychromatic418967fa.accept_17_1_2_16_1_5596 52 189
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 189 288 3 17 63 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 189 288
  (Polychromatic418967fa.accept_15_5_9_3_1_528 50 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 189 288 (Polychromatic418967fa.accept_19_11_18_3_1_1755 49 189 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 189 288 3 16 63 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 189 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 189 288 (Polychromatic418967fa.accept_25_21_14_13_1_17685 46 189 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 189 288 9 5 21 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 189 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 44 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 189 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 43 189 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 189 288 3 14 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 189 288 (Polychromatic418967fa.accept_10_1_9_8_1_123
  41 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 288
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 40 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 189 288 3 13 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 189 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 38 189 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 189 288 9 4 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 189 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 189 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 189
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 189 288 3 11 63 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 189 288
  (Polychromatic418967fa.accept_22_10_13_2_1_13227 32 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 189 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 189 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 189 288 3 10 63 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 189 288
  (Polychromatic418967fa.accept_14_1_7_8_1_2063 29 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 189 288 (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 189 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 189 288 9 3 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 189 288
  (Polychromatic418967fa.accept_22_4_13_2_1_16231 26 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 189 288 (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 189 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 189 288 3 8 63 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 189 288
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 22 189 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 189 288 3 7 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 189 288 (Polychromatic418967fa.accept_14_6_7_8_1_624
  20 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 288
  (Polychromatic418967fa.accept_20_19_9_8_1_12192 19 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 189 288 9 2 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 189 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 189 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 288
  (Polychromatic418967fa.accept_19_16_18_3_1_15081 16 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 189 288 3 5 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 189 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 189 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 288
  (Polychromatic418967fa.accept_14_13_7_8_1_677 13 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 189 288 3 4 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 189 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 189 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 288 (Polychromatic418967fa.accept_15_10_9_3_1_1947 10 189
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 189 288 9 1 21 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 189 288
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 189 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 189 288 3 2 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 189 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 5 189 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 4 189 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 189 288 3 1 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 189 288 (Polychromatic418967fa.accept_19_2_18_3_1_5517 2 189 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 189 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 188 288 (Eq.refl Bool.true) (allA_succ_of_gcd 100 188 288 4 25 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 188 288 (Polychromatic418967fa.accept_13_8_6_2_1_865
  99 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 188 288 2 49 94 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 188 288
  (accept_3_4 97 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 188 288 4 24 47 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 188 288
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 95 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 188 288 2 47 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 188 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 188 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 188 288 4 23 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 188 288 (accept_3_4 91 188 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 188 288 2 45 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 188 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 89
  188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 188 288 4 22 47 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 188 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 87 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 188 288 2 43 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 188 288 (accept_3_4 85 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 188 288 4 21 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 188 288 (Polychromatic418967fa.accept_17_15_1_16_1_8166 83 188 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 188 288 2 41 94 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 188 288
  (Polychromatic418967fa.accept_19_5_17_3_1_4152 81 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 188 288 4 20 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 188 288 (accept_3_4 79 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 188 288 2 39 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 188 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 77 188 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 188 288 4 19 47 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 188 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 188 288 2 37 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 188 288 (accept_3_4 73 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 188 288 4 18 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 188 288 (Polychromatic418967fa.accept_15_11_8_3_1_1943 71 188 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 188 288 2 35 94 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 188 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 69 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 188 288 4 17 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 188 288 (accept_3_4 67 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 188 288 2 33 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 188 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 188 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 188 288 4 16 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 188 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 63 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 188 288 2 31 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 188 288 (accept_3_4 61 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 188 288 4 15 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 188 288 (Polychromatic418967fa.accept_19_2_17_3_1_11224 59 188 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 188 288 2 29 94 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 188 288
  (Polychromatic418967fa.accept_15_12_8_3_1_1995 57 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 188 288 4 14 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 188 288 (accept_3_4 55 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 188 288 2 27 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 188 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 53 188 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 188 288 4 13 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 188 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 188 288 2 25 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 188 288 (accept_3_4 49 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 188 288 4 12 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 188 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 188 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 188 288 2 23 94 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 188 288
  (Polychromatic418967fa.accept_22_1_12_2_1_11707 45 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 188 288 4 11 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 188 288 (accept_3_4 43 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 188 288 2 21 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 188 288 (Polychromatic418967fa.accept_15_11_8_3_1_1943 41 188 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 188 288 4 10 47 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 188 288
  (Polychromatic418967fa.accept_15_9_8_3_1_557 39 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 188 288 2 19 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 188 288 (accept_3_4 37 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 188 288 4 9 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 188 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 188 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 288 2 17 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 33
  188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 188 288 4 8 47 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 188 288 (accept_3_4 31
  188 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 188 288 2 15 94 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 188 288
  (Polychromatic418967fa.accept_17_12_1_16_1_4360 29 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 188 288 4 7 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 188 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 188 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 188 288 2 13 94 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 188 288 (accept_3_4 25 188 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 188 288 4 6 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 188 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 188 288 2 11 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 188 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 188 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 188 288 4 5 47 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 188 288 (accept_3_4 19 188 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 188 288 2 9 94 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 188 288
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 188 288 4 4 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 188 288 (Polychromatic418967fa.accept_17_15_1_16_1_8166 15 188 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 188 288 2 7 94 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 188 288 (accept_3_4 13 188 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 188 288 4 3 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 188 288 (Polychromatic418967fa.accept_15_11_8_3_1_1943
  11 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 288 2 5 94 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 288 4 2 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 288 (accept_3_4 7 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  288 2 3 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 188 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 288 4 1 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 188 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 188 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 288 2 1 94 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 288 (accept_3_4 1 188 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 188
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 187 288 (Eq.refl Bool.true) (allA_succ_of_accept 101 187 288 (accept_3_5 101 187 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 187 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 100 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 187 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 99 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 187 288 (accept_3_5 98 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 187 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 97 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 187 288 (Polychromatic418967fa.accept_19_1_16_3_1_11223 96 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 187 288 (accept_3_5 95 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 187 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 94 187 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 187 288
  (Polychromatic418967fa.accept_19_17_16_3_1_8401 93 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 187 288 (accept_3_5 92 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 187 288 (Polychromatic418967fa.accept_19_15_16_3_1_8409 91 187 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 187 288 (Polychromatic418967fa.accept_7_6_5_1_1_416
  90 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 187 288 (accept_3_5 89
  187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 187 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 88 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 187 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 187 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 187 288 (accept_3_5 86 187 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 187 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 85 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 187 288
  (Polychromatic418967fa.accept_23_15_3_12_1_17818 84 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 187 288 (accept_3_5 83 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 187 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 82 187 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 187 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 187 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 187 288 (accept_3_5 80 187 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 187 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184
  79 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 187 288
  (Polychromatic418967fa.accept_19_2_16_3_1_7005 78 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 187 288 (accept_3_5 77 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 187 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 187 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 75 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 187 288 (accept_3_5 74 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 187 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 187 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 187 288
  (Polychromatic418967fa.accept_13_7_5_2_1_401 72 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 187 288 (accept_3_5 71 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 187 288 (Polychromatic418967fa.accept_15_10_7_3_1_1939 70 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 187 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 187 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 187 288 (accept_3_5 68 187 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 187 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 187 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 187 288 (accept_3_5 65 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 187 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 64 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 187 288 (Polychromatic418967fa.accept_19_6_16_3_1_1801 63 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 187 288 (accept_3_5 62 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 187 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 61 187
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 187 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 187 288 (accept_3_5 59 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 187 288 (Polychromatic418967fa.accept_19_1_16_3_1_11223 58 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 187 288 (Polychromatic418967fa.accept_15_12_7_3_1_1940 57 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 187 288 (accept_3_5 56 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 187 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 187 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 187 288
  (Polychromatic418967fa.accept_21_12_19_15_1_8942 54 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 187 288 (accept_3_5 53 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 187 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 187 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 187 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 51 187
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 187 288 (accept_3_5 50 187
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 187 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 187 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 187 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 187 288 (accept_3_5 47 187 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 187 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 187 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 187 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 45
  187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 187 288 (accept_3_5 44
  187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 187 288
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 43 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 187 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 42 187 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 288 (accept_3_5 41 187 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 187 288 (Polychromatic418967fa.accept_15_10_7_3_1_1939 40 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 187 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 187 288 (accept_3_5 38 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 187 288 (Polychromatic418967fa.accept_19_18_16_3_1_1803 37 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 187 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 288 (accept_3_5 35 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 187 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 187 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 187 288
  (Polychromatic418967fa.accept_13_7_5_2_1_401 33 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 187 288 (accept_3_5 32 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 187 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 187 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 187 288 (accept_3_5 29 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 187 288 (Polychromatic418967fa.accept_21_7_19_15_1_4201 28 187
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 187 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 187 288 (accept_3_5 26 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 187 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 187 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 187 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 288 (accept_3_5 23 187 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 187 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 22 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 288
  (Polychromatic418967fa.accept_19_2_16_3_1_7005 21 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 187 288 (accept_3_5 20 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 187 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 187 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 288 (accept_3_5 17 187 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 16 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 288 (accept_3_5 14 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 288 (accept_3_5 11 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 187 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 288 (accept_3_5 8 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 187 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 288 (accept_3_5 5 187 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 187 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 288 (accept_3_5 2 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 288 (Polychromatic418967fa.accept_19_1_16_3_1_11223 1 187 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 186 288 (Eq.refl Bool.true) (allA_succ_of_gcd 102 186 288 6 17 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 186 288 (Polychromatic418967fa.accept_7_3_4_1_1_71
  101 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 186 288 2 50 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 186 288 3 33 62
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 186 288 2 49
  93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 186 288
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 97 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 186 288 6 16 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 186 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 95 186 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 186 288 2 47 93 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 186 288 3 31 62 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 186 288 2 46 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 186 288
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 91 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 186 288 6 15 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 186 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 186 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 186 288 2 44 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 186 288 3 29 62 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 186 288 2 43 93 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 186 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 85 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 186 288 6 14 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 186 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 83 186 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 186 288 2 41 93 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 186 288 3 27 62 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 186 288 2 40 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 186 288
  (Polychromatic418967fa.accept_21_16_18_15_1_7282 79 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 186 288 6 13 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 186 288 (Polychromatic418967fa.accept_13_12_4_2_1_2955 77 186 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 186 288 2 38 93 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 186 288 3 25 62 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 186 288 2 37 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 186 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 186 288 6 12 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 186 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 71 186 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 186 288 2 35 93 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 186 288 3 23 62 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 186 288 2 34 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 186 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 67 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 186 288 6 11 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 186 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 65 186 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 186 288 2 32 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 186 288 3 21 62 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 186 288 2 31 93 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 186 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 61 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 186 288 6 10 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 186 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 186 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 186 288 2 29 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 186 288 3 19 62 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 186 288 2 28 93 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 186 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 55 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 186 288 6 9 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 186 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 186 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 186 288 2 26 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 186 288 3 17 62 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 186 288 2 25 93 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 186 288
  (Polychromatic418967fa.accept_21_7_18_15_1_2887 49 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 186 288 6 8 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 186 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 186 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 186 288 2 23 93 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 186 288 3 15 62 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 186 288 2 22 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 186 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 288 6 7 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 186 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 41 186 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 186 288 2 20 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 186 288 3 13 62 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 186 288 2 19 93 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 186 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 37 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 288 6 6 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 186 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 186 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 186 288 2 17 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 186 288 3 11 62 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 186 288 2 16 93 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 288 6 5 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 186 288 (Polychromatic418967fa.accept_19_10_15_3_1_5470 29 186 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 288 2 14 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 186 288 3 9 62 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 186 288 2 13 93 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 186 288
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 25 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 288 6 4 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 186 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 186 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 288 2 11 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 186 288 3 7 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 186 288 2 10 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 288 6 3 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 186 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 186 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 288 2 8 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 186 288 3 5 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 186 288 2 7 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 288 6 2 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 186 288 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 186 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 288 2 5 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 186 288 3 3 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 186 288 2 4 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 288 (Polychromatic418967fa.accept_19_7_15_3_1_2896
  7 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 288 6 1 31 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 186 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 186 288 2 2 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 186 288 3 1 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 186 288 2 1 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 186 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 186 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 186
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 185 288 (Eq.refl Bool.true) (allA_succ_of_accept 103 185 288 (accept_3_4 103 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 185 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 102 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 185 288
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 101 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 185 288 (accept_3_4 100 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 185 288 (Polychromatic418967fa.accept_15_9_5_3_1_554 99 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 185 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 98 185
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 185 288 (accept_3_4 97 185
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 185 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 96 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 185 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 185 288 (accept_3_4 94 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 185 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 185 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 185 288 (Polychromatic418967fa.accept_10_2_5_8_1_139
  92 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 185 288 (accept_3_4 91
  185 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 185 288
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 90 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 185 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 185 288 (accept_3_4 88 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 185 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 87 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 185 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 86 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 185 288 (accept_3_4 85 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 185 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 84 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 185 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 83 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 185 288 (accept_3_4 82 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 185 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 185 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 185 288
  (Polychromatic418967fa.accept_23_11_1_12_1_16211 80 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 185 288 (accept_3_4 79 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 185 288 (Polychromatic418967fa.accept_23_9_1_12_1_9755 78 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 185 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 77 185
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 185 288 (accept_3_4 76 185
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 185 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 185 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 185 288 (accept_3_4 73 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 185 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 185 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 185 288
  (Polychromatic418967fa.accept_21_8_17_15_1_2834 71 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 185 288 (accept_3_4 70 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 185 288 (Polychromatic418967fa.accept_15_9_5_3_1_554 69 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 185 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 185 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 185 288 (accept_3_4 67 185 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 185 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429
  66 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 185 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 185 288 (accept_3_4 64 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 185 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 185 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 185 288 (accept_3_4 61 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 185 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 185 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 185 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 59 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 185 288 (accept_3_4 58 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 185 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 57 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 185 288 (Polychromatic418967fa.accept_19_18_14_3_1_8427 56 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 185 288 (accept_3_4 55 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 185 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 185 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 185 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 185 288 (accept_3_4 52 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 185 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 185 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 50 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 185 288 (accept_3_4 49 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 185 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 185
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 185 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 185 288 (accept_3_4 46 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 185 288 (Polychromatic418967fa.accept_17_11_15_16_1_4377 45 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 185 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 185 288 (accept_3_4 43 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 185 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 185
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 185 288
  (Polychromatic418967fa.accept_27_14_23_18_1_10356 41 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 185 288 (accept_3_4 40 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 185 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 185 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 38 185
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 185 288 (accept_3_4 37 185
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 185 288
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 185 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 35 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 185 288 (accept_3_4 34 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 185 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 185 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 185 288 (accept_3_4 31
  185 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 185 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 185 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 288 (accept_3_4 28 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 185 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 288 (accept_3_4 25 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 185 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 288 (accept_3_4 22 185 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 288 (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 185 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 288
  (Polychromatic418967fa.accept_23_20_1_12_1_17817 20 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 185 288 (accept_3_4 19 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 185 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 185
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 288 (accept_3_4 16 185
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 15 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 185 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 288 (accept_3_4 13 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 185 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 185 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 288 (accept_3_4 10
  185 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 185 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 8 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 288 (accept_3_4 7 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 185 288 (Polychromatic418967fa.accept_15_6_5_3_1_1988 6 185 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5
  185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 288 (accept_3_4 4 185
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 185 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 185 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 288 (accept_3_4 1 185 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 185
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 184 288 (Eq.refl Bool.true) (allA_succ_of_gcd 104 184 288 8 13 23 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 184 288
  (Polychromatic418967fa.accept_19_8_13_3_1_4172 103 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 184 288 2 51 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 184 288 (accept_3_5 101 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 184 288 4 25 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 184 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 99 184 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 184 288 2 49 92 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 184 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 97 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 184 288 8 12 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 184 288 (accept_3_5 95 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 184 288 2 47 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 184 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 93 184 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 184 288 4 23 46 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 184 288
  (Polychromatic418967fa.accept_15_1_4_3_1_1928 91 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 184 288 2 45 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 184 288 (accept_3_5 89 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 184 288 8 11 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 184 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 184 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 184 288 2 43 92 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 184 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 85 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 184 288 4 21 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 184 288 (accept_3_5 83 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 184 288 2 41 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 184 288 (Polychromatic418967fa.accept_21_18_16_15_1_2864 81 184 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 184 288 8 10 23 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 184 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 79 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 184 288 2 39 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 184 288 (accept_3_5 77 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 184 288 4 19 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 184 288 (Polychromatic418967fa.accept_28_19_16_8_1_17816 75 184 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 184 288 2 37 92 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 184 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 184 288 8 9 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 184 288 (accept_3_5 71 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  184 288 2 35 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 184 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 184 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 184 288 4 17 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 184 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930
  67 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 184 288 2 33 92 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 184 288
  (accept_3_5 65 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 184 288 8 8 23 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 184 288
  (Polychromatic418967fa.accept_27_9_22_18_1_17815 63 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 184 288 2 31 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 184 288 (Polychromatic418967fa.accept_15_1_4_3_1_1928 61 184 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 184 288 4 15 46 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 184 288 (accept_3_5 59 184 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 184 288 2 29 92 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 184 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 57 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 184 288 8 7 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 184 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 184 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 184 288 2 27 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 184 288 (accept_3_5 53 184 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 184 288 4 13 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 184 288 (Polychromatic418967fa.accept_21_9_16_15_1_9014 51 184
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 184 288 2 25 92 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 184 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 184 288 8 6 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 184 288 (accept_3_5 47 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  184 288 2 23 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 184 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 184 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 184 288 4 11 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 184 288 (Polychromatic418967fa.accept_14_1_2_8_1_655
  43 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 184 288 2 21 92 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 184 288
  (accept_3_5 41 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 184 288 8 5 23 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 184 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 184 288 2 19 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 184 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 37 184 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 184 288 4 9 46 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 184 288 (accept_3_5 35 184 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 184 288 2 17 92 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 184 288
  (Polychromatic418967fa.accept_22_11_8_2_1_8450 33 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 184 288 8 4 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 184 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 184 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 184 288 2 15 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 184 288 (accept_3_5 29 184 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 184 288 4 7 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 184 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 184 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 288 2 13 92 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 288
  (Polychromatic418967fa.accept_17_8_14_16_1_6849 25 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 184 288 8 3 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 184 288 (accept_3_5 23 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 184 288 2 11 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 184 288 (Polychromatic418967fa.accept_22_21_8_2_1_16285 21 184 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 184 288 4 5 46 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 184 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 184 288 2 9 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 184 288 (accept_3_5 17 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 184 288 8 2 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 184 288 (Polychromatic418967fa.accept_14_1_2_8_1_655 15 184 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 288 2 7 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 184 288 4 3 46 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 184 288 (accept_3_5 11
  184 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 184 288 2 5 92 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 184 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 184 288 8 1 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 184 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 184 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 184 288 2 3 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 184 288 (accept_3_5 5 184 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184 288 4 1 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 184 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 184 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 184 288 2 1 92 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 184 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 1 184 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 184
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 183 288 (Eq.refl Bool.true) (allA_succ_of_gcd 105 183 288 3 35 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 183 288
  (Polychromatic418967fa.accept_19_9_12_3_1_2950 104 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 183 288 (Polychromatic418967fa.accept_13_12_1_2_1_845 103 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 183 288 3 34 61 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 183 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 101 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 183 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 100 183 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 183 288 3 33 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 183 288
  (Polychromatic418967fa.accept_20_18_3_8_1_7903 98 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 183 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 97 183 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 183 288 3 32 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 183 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165
  95 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 183 288
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 94 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 183 288 3 31 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 183 288 (Polychromatic418967fa.accept_25_17_8_13_1_17758 92 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 183 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 91 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 183 288 3 30 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 183 288 (Polychromatic418967fa.accept_19_13_12_3_1_5540 89 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 183 288
  (Polychromatic418967fa.accept_17_3_13_16_1_2183 88 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 87 183 288 3 29 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 86 183 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 86 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 183 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 85 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 183 288 3 28 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 183 288 (Polychromatic418967fa.accept_19_7_12_3_1_4169 83 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 183 288
  (Polychromatic418967fa.accept_23_13_22_12_1_11395 82 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 81 183 288 3 27 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 80 183 288 (Polychromatic418967fa.accept_17_12_13_16_1_3226 80 183 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 183 288
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 79 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 183 288 3 26 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 183 288 (Polychromatic418967fa.accept_13_12_1_2_1_845 77 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 183 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 76 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 183 288 3 25 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 183 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 74 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 183 288
  (Polychromatic418967fa.accept_20_13_3_8_1_4865 73 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 183 288 3 24 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 183 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 71 183 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 183 288
  (Polychromatic418967fa.accept_19_13_12_3_1_5540 70 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 183 288 3 23 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 183 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 68 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 183 288
  (Polychromatic418967fa.accept_19_10_12_3_1_12558 67 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 183 288 3 22 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 183 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 65 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 183 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 183 288 3 21 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 183 288 (Polychromatic418967fa.accept_22_18_7_2_1_10017 62 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 183 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 61 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 183 288 3 20 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 183 288 (Polychromatic418967fa.accept_19_2_12_3_1_5446 59 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 183 288
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 58 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 183 288 3 19 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 183 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 183 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 55 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 183 288 3 18 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 183 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 53 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 288
  (Polychromatic418967fa.accept_23_6_22_12_1_17814 52 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 183 288 3 17 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 183 288 (Polychromatic418967fa.accept_27_23_21_18_1_6228 50 183 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 288
  (Polychromatic418967fa.accept_14_7_1_8_1_2873 49 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 183 288 3 16 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 183 288 (Polychromatic418967fa.accept_19_9_12_3_1_2950 47 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 183 288 3 15 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 183 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 44 183 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 288
  (Polychromatic418967fa.accept_17_9_13_16_1_3266 43 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 183 288 3 14 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 183 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 41 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 288
  (Polychromatic418967fa.accept_19_2_12_3_1_5446 40 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 183 288 3 13 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 183 288 (Polychromatic418967fa.accept_13_12_1_2_1_845 38 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 288
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 37 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 183 288 3 12 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 183 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 288
  (Polychromatic418967fa.accept_19_15_12_3_1_11213 34 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 183 288 3 11 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 183 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464 32 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 31 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 183 288 3 10 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 183 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 29 183 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 288
  (Polychromatic418967fa.accept_19_9_12_3_1_2950 28 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 183 288 3 9 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 183 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 183 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 183
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 183 288 3 8 61 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 183 288
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 23 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 22 183 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 183 288 3 7 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 183 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068
  20 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 288
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 183 288 3 6 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 183 288 (Polychromatic418967fa.accept_19_17_12_3_1_12555 17 183 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  16 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 183 288 3 5 61 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 183 288
  (Polychromatic418967fa.accept_20_14_3_8_1_4914 14 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 288 (Polychromatic418967fa.accept_19_13_12_3_1_5540 13 183 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 288 3 4 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 11 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 288 (Polychromatic418967fa.accept_19_10_12_3_1_12558 10 183 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 183 288 3 3 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 183 288
  (Polychromatic418967fa.accept_27_8_21_18_1_17813 8 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 183 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873 7 183 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 183 288 3 2 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 183 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5
  183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 288
  (Polychromatic418967fa.accept_28_4_15_8_1_17812 4 183 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 183 288 3 1 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 183 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 2 183 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 183 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 182 288 (Eq.refl Bool.true) (allA_succ_of_gcd 106 182 288 2 53 91 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 182 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 105 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 182 288 2 52 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 182 288 (accept_3_4 103 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 182 288 2 51 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 182 288 (Polychromatic418967fa.accept_21_17_14_15_1_5750 101 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 182 288 2 50 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 182 288
  (Polychromatic418967fa.accept_19_4_11_3_1_13801 99 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 182 288 2 49 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 182 288 (accept_3_4 97 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 182 288 2 48 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 182 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 95 182 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 182 288 2 47 91 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 182 288
  (Polychromatic418967fa.accept_21_9_14_15_1_11910 93 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 182 288 2 46 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 182 288 (accept_3_4 91 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 182 288 2 45 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 182 288 (Polychromatic418967fa.accept_15_14_2_3_1_1980 89 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 182 288 2 44 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 182 288
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 87 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 182 288 2 43 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 182 288 (accept_3_4 85 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 182 288 2 42 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 182 288 (Polychromatic418967fa.accept_21_20_14_15_1_13468 83 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 182 288 2 41 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 182 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 81 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 182 288 2 40 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 182 288 (accept_3_4 79 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 182 288 2 39 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 182 288 (Polychromatic418967fa.accept_19_1_11_3_1_5463 77 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 182 288 2 38 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 182 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 75 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 182 288 2 37 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 182 288 (accept_3_4 73 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 182 288 2 36 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 182 288 (Polychromatic418967fa.accept_19_14_11_3_1_5508 71 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 182 288 2 35 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 182 288
  (Polychromatic418967fa.accept_17_1_12_16_1_2211 69 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 182 288 2 34 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 182 288 (accept_3_4 67 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 182 288 2 33 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 182 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 182 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 182 288 2 32 91 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 182 288
  (Polychromatic418967fa.accept_22_19_6_2_1_16233 63 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 182 288 2 31 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 182 288 (accept_3_4 61 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 182 288 2 30 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 182 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 59 182 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 182 288 2 29 91 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 182 288
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 57 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 182 288 2 28 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 182 288 (accept_3_4 55 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 182 288 2 27 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 182 288 (Polychromatic418967fa.accept_44_9_6_24_1_17811 53 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 182 288 2 26 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 182 288
  (Polychromatic418967fa.accept_19_13_11_3_1_5465 51 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 182 288 2 25 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 182 288 (accept_3_4 49 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 182 288 2 24 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 182 288 (Polychromatic418967fa.accept_17_13_12_16_1_6908 47 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 182 288 2 23 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 182 288 2 22 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 182 288 (accept_3_4 43 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 182 288 2 21 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 182 288 (Polychromatic418967fa.accept_21_20_14_15_1_13468 41 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 288 2 20 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 182 288
  (Polychromatic418967fa.accept_19_1_11_3_1_5463 39 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 182 288 2 19 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 182 288 (accept_3_4 37 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 182 288 2 18 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 182 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 182 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 182 288 2 17 91 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 182 288
  (Polychromatic418967fa.accept_19_14_11_3_1_5508 33 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 182 288 2 16 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 182 288 (accept_3_4 31 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 182 288 2 15 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 182 288 (Polychromatic418967fa.accept_15_14_2_3_1_1980 29 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 288 2 14 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 288
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 288 2 13 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 182 288 (accept_3_4 25 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 182 288 2 12 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 182 288 (Polychromatic418967fa.accept_19_4_11_3_1_13801 23 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 288 2 11 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 288
  (Polychromatic418967fa.accept_19_2_11_3_1_4136 21 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 182 288 2 10 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 182 288 (accept_3_4 19 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 288 2 9 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 288 (Polychromatic418967fa.accept_21_17_14_15_1_5750 17 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 288 2 8 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 182 288 2 7 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 182 288 (accept_3_4 13 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 288 2 6 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 288 (Polychromatic418967fa.accept_17_11_12_16_1_3219 11 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 288 2 5 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 288
  (Polychromatic418967fa.accept_19_9_11_3_1_5580 9 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 288 2 4 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 288 (accept_3_4 7 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  288 2 3 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 182 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 288 2 2 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 288 (Polychromatic418967fa.accept_21_3_14_15_1_10526 3 182 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 288 2 1 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 288 (accept_3_4 1 182 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 181 288 (Eq.refl Bool.true) (allA_succ_of_accept 107 181 288 (accept_3_5 107 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 181 288 (Polychromatic418967fa.accept_19_11_10_3_1_2934 106
  181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 181 288
  (Polychromatic418967fa.accept_13_1_12_2_1_384 105 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 181 288 (accept_3_5 104 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 181 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 103 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 181 288 (Polychromatic418967fa.accept_19_7_10_3_1_4149 102 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 181 288 (accept_3_5 101 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 181 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 100 181
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 181 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 99 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 181 288 (accept_3_5 98 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 181 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 97 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 181 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 181 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 181 288 (accept_3_5 95 181 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 181 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 94 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 181 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 93 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 181 288 (accept_3_5 92 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 181 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 91 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 181 288 (Polychromatic418967fa.accept_17_5_11_16_1_3257 90 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 181 288 (accept_3_5 89 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 181 288 (Polychromatic418967fa.accept_13_10_12_2_1_1460 88 181
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 181 288
  (Polychromatic418967fa.accept_19_11_10_3_1_2934 87 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 181 288 (accept_3_5 86 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 181 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 85 181 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 181 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 84 181
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 181 288 (accept_3_5 83 181
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 181 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 82 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 181 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 81 181 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 181 288 (accept_3_5 80 181 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 181 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 181 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 181 288
  (Polychromatic418967fa.accept_20_18_1_8_1_9326 78 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 181 288 (accept_3_5 77 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 181 288 (Polychromatic418967fa.accept_22_10_5_2_1_16254 76 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 181 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 181 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 181 288 (accept_3_5 74 181 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 181 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 73 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 181 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 72 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 181 288 (accept_3_5 71 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 181 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 70 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 181 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 69 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 181 288 (accept_3_5 68 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 181 288 (Polychromatic418967fa.accept_20_7_1_8_1_10806 67 181
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 181 288
  (Polychromatic418967fa.accept_13_1_12_2_1_384 66 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 181 288 (accept_3_5 65 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 181 288 (Polychromatic418967fa.accept_15_4_1_3_1_1922 64 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 181 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 63 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 181 288 (accept_3_5 62 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 181 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 181 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 181 288
  (Polychromatic418967fa.accept_21_18_13_15_1_2884 60 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 181 288 (accept_3_5 59 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 181 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 181 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 181 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 57 181
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 181 288 (accept_3_5 56 181
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 181 288
  (Polychromatic418967fa.accept_13_3_12_2_1_385 55 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 181 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 181 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 181 288 (accept_3_5 53 181 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 181 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 181 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 181 288 (accept_3_5 50 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 181 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 181 288 (Polychromatic418967fa.accept_17_14_11_16_1_3261 48 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 288 (accept_3_5 47 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 181 288 (Polychromatic418967fa.accept_17_12_11_16_1_6903 46
  181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 181 288
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 45 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 181 288 (accept_3_5 44 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 181 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 43 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 181 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 42 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 288 (accept_3_5 41 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 181 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 39 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 181 288 (accept_3_5 38 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 181 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 181 288 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 288 (accept_3_5 35 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 288 (Polychromatic418967fa.accept_15_4_1_3_1_1922 34 181
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 288 (accept_3_5 32 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 31 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 181 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 288 (accept_3_5 29 181 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 288 (Polychromatic418967fa.accept_15_13_1_3_1_1972 28 181 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 288
  (Polychromatic418967fa.accept_13_1_12_2_1_384 27 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 288 (accept_3_5 26 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 288 (Polychromatic418967fa.accept_22_3_5_2_1_17810 25 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 288 (Polychromatic418967fa.accept_19_5_10_3_1_5460 24 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 288 (accept_3_5 23 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 288 (Polychromatic418967fa.accept_17_5_11_16_1_3257 22 181
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 288
  (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 288 (accept_3_5 20 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 288 (accept_3_5 17 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 181 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 288
  (Polychromatic418967fa.accept_17_15_11_16_1_3263 15 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 181 288 (accept_3_5 14 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 181 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 181 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 181 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 181 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 288 (accept_3_5 11 181 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 288
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 10 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 181 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 181 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 288 (accept_3_5 8 181 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 181 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 7 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 181 288
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 181 288 (accept_3_5 5 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  181 288 (Polychromatic418967fa.accept_13_4_12_2_1_1459 4 181 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 181 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 181 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 288 (accept_3_5 2 181 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 288 (Polychromatic418967fa.accept_13_1_12_2_1_384 1 181 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 181
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 180 288 (Eq.refl Bool.true) (allA_succ_of_gcd 108 180 288 36 3 5 8 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 180 288
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 107 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 180 288 2 53 90 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 105 180 288 3 35 60 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 180 288 4 26 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 180 288
  (Polychromatic418967fa.accept_21_19_12_15_1_7307 103 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 180 288 6 17 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 180 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 180 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 180 288 4 25 45 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 180 288 9 11 20 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 180 288 2 49 90 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 180 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 97 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 180 288 12 8 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 180 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 180 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 180 288 2 47 90 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 180 288 3 31 60 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 180 288 4 23 45 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 180 288
  (Polychromatic418967fa.accept_17_6_10_16_1_9453 91 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 180 288 18 5 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 180 288 (Polychromatic418967fa.accept_19_13_9_3_1_9806 89 180 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 180 288 4 22 45 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 180 288 3 29 60 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 180 288 2 43 90 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 180 288
  (Polychromatic418967fa.accept_21_1_12_15_1_2880 85 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 180 288 12 7 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 180 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 180 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 180 288 2 41 90 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 180 288 9 9 20 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 180 288 4 20 45 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 180 288
  (Polychromatic418967fa.accept_22_13_4_2_1_3601 79 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 180 288 6 13 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 180 288 (Polychromatic418967fa.accept_17_9_10_16_1_3217 77 180 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 180 288 4 19 45 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 180 288 3 25 60 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 180 288 2 37 90 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 180 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 180 288 36 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 180 288 (Polychromatic418967fa.accept_19_14_9_3_1_13821 71 180 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 180 288 2 35 90 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 180 288 3 23 60 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 180 288 4 17 45 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 180 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 180 288 6 11 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 180 288 (Polychromatic418967fa.accept_22_21_4_2_1_8487 65 180 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 180 288 4 16 45 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 180 288 9 7 20 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 180 288 2 31 90 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 180 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 61 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 180 288 12 5 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 180 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 180 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 180 288 2 29 90 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 180 288 3 19 60 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 180 288 4 14 45 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 180 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 180 288 18 3 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 180 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 180 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 180 288 4 13 45 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 180 288 3 17 60 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 180 288 2 25 90 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 180 288
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 49 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 180 288 12 4 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 180 288 (Polychromatic418967fa.accept_21_5_12_15_1_11875 47 180 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 288 2 23 90 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 180 288 9 5 20 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 180 288 4 11 45 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 43 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 288 6 7 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 180 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 180 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 288 4 10 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 180 288 3 13 60 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 180 288 2 19 90 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 288
  (Polychromatic418967fa.accept_19_18_9_3_1_8430 37 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 288 36 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 180 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 180 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 288 2 17 90 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 180 288 3 11 60 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 180 288 4 8 45 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 288 6 5 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 180 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 180 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 288 4 7 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 180 288 9 3 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 180 288 2 13 90 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 288 12 2 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 180 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 180 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 288 2 11 90 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 180 288 3 7 60 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 180 288 4 5 45 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 288
  (Polychromatic418967fa.accept_21_19_12_15_1_7307 19 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 180 288 18 1 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 180 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 180 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 288 4 4 45 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 288 3 5 60 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 288 2 7 90 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 288 12 1 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 180 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 180 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 288 2 5 90 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 180 288 9 1 20 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 180 288 4 2 45 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 288
  (Polychromatic418967fa.accept_17_7_10_16_1_5582 7 180 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 288 6 1 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 288 (Polychromatic418967fa.accept_21_5_12_15_1_11875 5 180 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 288 4 1 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 180 288 3 1 60 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 180 288 2 1 90 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 288 (Polychromatic418967fa.accept_21_1_12_15_1_2880 1 180
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 179 288 (Eq.refl Bool.true) (allA_succ_of_accept 109 179 288 (accept_3_4 109 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 179 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 108 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 179 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 107 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 179 288 (accept_3_4 106 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 179 288 (Polychromatic418967fa.accept_23_13_18_12_1_8033 105 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 179 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 104 179 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 179 288 (accept_3_4 103 179 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 179 288
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 102 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 179 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 179 288 (accept_3_4 100 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 179 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 99 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 179 288
  (Polychromatic418967fa.accept_17_13_9_16_1_3254 98 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 179 288 (accept_3_4 97 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 179 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 96 179 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 179 288 (Polychromatic418967fa.accept_17_10_9_16_1_5607 95 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 179 288 (accept_3_4 94 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 179 288
  (Polychromatic418967fa.accept_17_8_9_16_1_6844 93 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 179 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 92 179 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 179 288 (accept_3_4 91 179 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 179 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 90 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 179 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 89 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 179 288 (accept_3_4 88 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 179 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 179 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 86 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 179 288 (accept_3_4 85 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 179 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 179 288
  (Polychromatic418967fa.accept_13_5_10_2_1_856 83 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 179 288 (accept_3_4 82 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 179 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 81 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 179 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 179 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 179 288 (accept_3_4 79 179 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 179 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 78 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 179 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 77 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 179 288 (accept_3_4 76 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 179 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 179 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 74 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 179 288 (accept_3_4 73 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 179 288 (Polychromatic418967fa.accept_19_15_8_3_1_13786 72 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 179 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 71 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 179 288 (accept_3_4 70 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 179 288 (Polychromatic418967fa.accept_20_9_19_8_1_1151 69 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 179 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 179 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 179 288 (accept_3_4 67 179 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 179 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 179 288
  (Polychromatic418967fa.accept_22_21_3_2_1_16297 65 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 179 288 (accept_3_4 64 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 179 288 (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 179 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 179 288
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 62 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 179 288 (accept_3_4 61 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 179 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 60 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 179 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 179 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 179 288 (accept_3_4 58 179 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 179 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 179 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 56 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 179 288 (accept_3_4 55 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 179 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 179 288 (Polychromatic418967fa.accept_19_15_8_3_1_13786 53 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 288 (accept_3_4 52 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 179 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 179 288
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 50 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 179 288 (accept_3_4 49 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 179 288 (Polychromatic418967fa.accept_21_6_11_15_1_13454 48 179 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 179 288 (Polychromatic418967fa.accept_7_5_4_1_1_412
  47 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 288 (accept_3_4 46
  179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 179 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 179 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 179 288 (accept_3_4 43 179 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 179 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 42 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 41 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 179 288 (accept_3_4 40 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 179 288 (Polychromatic418967fa.accept_25_14_4_13_1_17809 39 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 288 (accept_3_4 37 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 179 288 (Polychromatic418967fa.accept_19_17_8_3_1_11211 36 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 288
  (Polychromatic418967fa.accept_27_8_17_18_1_17808 35 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 179 288 (accept_3_4 34 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 179 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 179 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 32 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 288 (accept_3_4 31 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 288
  (Polychromatic418967fa.accept_17_13_9_16_1_3254 30 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 288 (Polychromatic418967fa.accept_13_3_10_2_1_381 29 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 288 (accept_3_4 28 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 288 (accept_3_4 25 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 288 (accept_3_4 22 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 288
  (Polychromatic418967fa.accept_22_20_3_2_1_8507 20 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 288 (accept_3_4 19 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 179 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 288 (accept_3_4 16 179 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 288 (Polychromatic418967fa.accept_19_15_8_3_1_13786 15 179 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 288 (accept_3_4 13 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 288 (accept_3_4 10 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 288 (Polychromatic418967fa.accept_20_9_19_8_1_1151 9 179
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 288
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 8 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 288 (accept_3_4 7 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 288 (Polychromatic418967fa.accept_13_6_10_2_1_1449 6 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 179 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 288 (accept_3_4 4 179 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 179 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 288
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 288 (accept_3_4 1 179 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_288_segment_002))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


