-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch220_Segment000
-- name    : Polychromatic418967fa_Branch220_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:33:53.449194+00:00
-- url     : https://prove2.me/theorems/087ac27d-3fb9-4ca6-a9b7-031c215ba9c4
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

def Polychromatic418967fa.branch_220_segment_000 : allB 126 220 :=
  allB_succ' 96 125 220 (Eq.refl Bool.true) (allA_of_3_1 96 125 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  97 124 220 (Eq.refl Bool.true) (allA_succ_of_gcd 96 124 220 4 24 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 124 220 (accept_3_3 95 124 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 94 124 220 2 47 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 124 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 124 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 124 220 4 23 31 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 124 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 91 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 124 220 2 45 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 124 220 (accept_3_3 89 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 124 220 4 22 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 124 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 87 124 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 124 220 2 43 62 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 124 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 85 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 124 220 4 21 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 124 220 (accept_3_3 83 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 124 220 2 41 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 124 220 (Polychromatic418967fa.accept_15_6_4_10_1_2319 81 124 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 124 220 4 20 31 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 124 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 79 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 124 220 2 39 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 124 220 (accept_3_3 77 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 124 220 4 19 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 124 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 124 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 124 220 2 37 62 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 124 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 73 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 124 220 4 18 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 220 (accept_3_3 71 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 220 2 35 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 124 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 220 4 17 31 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 220
  (Polychromatic418967fa.accept_15_7_4_10_1_1513 67 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 220 2 33 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 220 (accept_3_3 65 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 220 4 16 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 220 (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 124 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 220 2 31 62 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 220
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 61 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 124 220 4 15 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 124 220 (accept_3_3 59 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 220 2 29 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 124 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 220 4 14 31 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 55 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 220 2 27 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 220 (accept_3_3 53 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 220 4 13 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 124 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 220 2 25 62 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 220
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 49 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 124 220 4 12 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 124 220 (accept_3_3 47 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 220 2 23 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 220 (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 124 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 220 4 11 31 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 220 2 21 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 220 (accept_3_3 41 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 220 4 10 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 124 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 220 2 19 62 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 220 4 9 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 124 220 (accept_3_3 35 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  124 220 2 17 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 124 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 124 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 220 4 8 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 220 (Polychromatic418967fa.accept_13_5_7_12_1_2757
  31 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 124 220 2 15 62 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 220
  (accept_3_3 29 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 220 4 7 31 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 220
  (Polychromatic418967fa.accept_19_8_10_11_1_7614 27 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 124 220 2 13 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 124 220 (Polychromatic418967fa.accept_18_7_16_4_1_1674 25 124 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 220 4 6 31 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 220 (accept_3_3 23 124 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 220 2 11 62 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 124 220 4 5 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 124 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 124 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 220 2 9 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 220 (accept_3_3 17 124 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 220 4 4 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 124 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 220 2 7 62 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 220
  (Polychromatic418967fa.accept_15_13_4_10_1_821 13 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 220 4 3 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 124 220 (accept_3_3 11 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  124 220 2 5 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 124 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 124 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 220 4 2 31 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 220 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 124 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 220 2 3 62 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 220 (accept_3_3 5
  124 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 220 4 1 31 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 124 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 124 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 124 220 2 1 62 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 124 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 124 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 124
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  123 220 (Eq.refl Bool.true) (allA_succ_of_accept 97 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 123 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 220
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 96 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 123 220 (accept_3_3 95 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 123 220 (Polychromatic418967fa.accept_28_10_11_24_1_13055 94 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 123 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 123 220 (accept_3_3 92 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 123 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 90 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 123 220 (accept_3_3 89 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 123 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 88 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 123 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 123 220 (accept_3_3 86 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 123 220 (accept_3_3 83 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 123 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 123 220 (Polychromatic418967fa.accept_15_6_3_10_1_2341 81 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 123 220 (accept_3_3 80 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 123 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 78 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 123 220 (accept_3_3 77 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 123 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 123 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 123 220 (accept_3_3 74 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 220
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 72 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 123 220 (accept_3_3 71 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 123 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 123 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 123 220 (accept_3_3 68 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 123 220 (accept_3_3 65 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 123 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 123 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 220 (accept_3_3 62 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 220
  (Polychromatic418967fa.accept_18_6_15_4_1_3916 60 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 123 220 (accept_3_3 59 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 123 220 (Polychromatic418967fa.accept_15_13_3_10_1_2296 58 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 123 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 220 (accept_3_3 56 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 123 220 (accept_3_3 53 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 123 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 123 220 (Polychromatic418967fa.accept_15_6_3_10_1_2341 51 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 220 (accept_3_3 50 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 123 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 123 220 (accept_3_3 47 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 123 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 123 220 (Polychromatic418967fa.accept_18_9_15_4_1_5173 45 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 220 (accept_3_3 44 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 123 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 123 220 (accept_3_3 41 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 123 220 (Polychromatic418967fa.accept_16_8_11_12_1_962 40 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 123 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 220 (accept_3_3 38 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 123 220 (accept_3_3 35 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 123 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 123 220 (Polychromatic418967fa.accept_13_7_6_12_1_2027 33 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 220 (accept_3_3 32 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 123 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 123 220 (accept_3_3 29 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 123 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 123 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 220 (accept_3_3 26 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 220
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 123 220 (accept_3_3 23 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 123 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 123 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 220 (accept_3_3 20 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 220 (accept_3_3 17 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 220 (accept_3_3 14 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 220 (accept_3_3 11 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 220 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 220 (accept_3_3 8 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 220 (accept_3_3 5 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 220 (Polychromatic418967fa.accept_16_4_11_12_1_1775 4 123 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 220 (accept_3_3 2 123 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 123 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  122 220 (Eq.refl Bool.true) (allA_of_3_1 99 122 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 121 220
  (Eq.refl Bool.true) (allA_succ_of_gcd 99 121 220 11 9 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 121 220 (accept_3_3 98 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 121 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 121 220 (Polychromatic418967fa.accept_7_5_2_3_1_106
  96 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 220 (accept_3_3 95
  121 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 220
  (Polychromatic418967fa.accept_12_10_1_4_1_392 94 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 121 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 121 220 (accept_3_3 92 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 121 220 (Polychromatic418967fa.accept_19_15_7_11_1_7657 91 121 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 121 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 90 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 121 220 (accept_3_3 89 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88
  121 220 11 8 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 87 121 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 121 220 (accept_3_3 86 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 121 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 121 220
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 84 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 121 220 (accept_3_3 83 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 121 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 121 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 121 220 (accept_3_3 80 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 121 220 (Polychromatic418967fa.accept_18_7_13_4_1_1670 79 121 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 121 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 78 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 121 220 11 7 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 121 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 75
  121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 121 220 (accept_3_3 74
  121 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 121 220
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 73 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 121 220 (Polychromatic418967fa.accept_13_7_4_12_1_1341 72 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 220 (accept_3_3 71 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 121 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 121 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 220 (accept_3_3 68 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 220 (Polychromatic418967fa.accept_13_2_4_12_1_745 67 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 121 220 11 6 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 121 220 (accept_3_3 65 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 121 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 121 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 220 (accept_3_3 62 121 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 220 (Polychromatic418967fa.accept_7_5_2_3_1_106
  61 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 220
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 60 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 121 220 (accept_3_3 59 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 121 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 121 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 220 (accept_3_3 56 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 55 121 220 11 5 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 121 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 121 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 220 (accept_3_3 53 121 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 220 (Polychromatic418967fa.accept_15_7_1_10_1_305
  52 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 220 (accept_3_3 50 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 220 (Polychromatic418967fa.accept_21_7_16_10_1_1349 49 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 220 (accept_3_3 47 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 121 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 121 220 11 4 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 121 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 220 (Polychromatic418967fa.accept_13_3_4_12_1_36
  42 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 220 (accept_3_3 41
  121 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 40 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 121 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 220 (accept_3_3 38 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 121 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 220 (Polychromatic418967fa.accept_7_1_2_3_1_257
  36 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 220 (accept_3_3 35
  121 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 34 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 121 220 11 3 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 121 220 (accept_3_3 32 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 121 220 (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 220 (Polychromatic418967fa.accept_21_9_16_10_1_5371 30 121
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 220 (accept_3_3 29 121
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 220
  (Polychromatic418967fa.accept_13_2_4_12_1_745 28 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 121 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 220 (accept_3_3 26 121 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 121 220 (Polychromatic418967fa.accept_17_8_2_16_1_5598 25 121 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 220
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 121 220 (accept_3_3 23 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 121 220 11 2 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 121 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 220 (accept_3_3 20 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 121 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 220
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 220 (accept_3_3 17 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 220 (Polychromatic418967fa.accept_13_3_4_12_1_36 16 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 220 (accept_3_3 14 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 121 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 121 220 11 1 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 121 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 121 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 220 (accept_3_3 8 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 220 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 220 (accept_3_3 5 121 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 220 (Polychromatic418967fa.accept_16_4_9_12_1_4829 4 121 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 220 (accept_3_3 2 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 121 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 120 220 (Eq.refl Bool.true) (allA_succ_of_gcd 100 120 220 20 5 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 120 220 (Polychromatic418967fa.accept_16_3_8_12_1_2736
  99 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 120 220 2 49 60 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 120 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 97 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 120 220 4 24 30 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 95 120 220 5 19 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 94 120 220 2 47 60 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 120 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 93 120 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 120 220 4 23 30 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 91 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 220 10 9 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 120 220 (accept_3_3 89 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 120 220 4 22 30 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 120 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 120 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 120 220 2 43 60 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 120 220 5 17 24 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 120 220 4 21 30 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 120 220 (accept_3_3 83
  120 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 220 2 41 60 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 120 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 120 220 20 4 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 120 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 120 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 120 220 2 39 60 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 120 220 (accept_3_3 77 120 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 220 4 19 30 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 120 220 5 15 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 120 220 2 37 60 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 120 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 73 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 220 4 18 30 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 120 220 (accept_3_3 71 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 120 220 10 7 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 120 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 120 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 120 220 4 17 30 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 67 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 220 2 33 60 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 120 220 5 13 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 120 220 4 16 30 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 120 220 (Polychromatic418967fa.accept_16_15_8_12_1_2737 63 120
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 120 220 2 31 60 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 220 20 3 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 120 220 (accept_3_3 59 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58
  120 220 2 29 60 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 120 220 (Polychromatic418967fa.accept_16_9_8_12_1_979 57 120 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 120 220 4 14 30 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 120 220 5 11 24 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 120 220 2 27 60 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 220 (accept_3_3 53 120 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 220 4 13 30 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 120 220 10 5 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 120 220 (Polychromatic418967fa.accept_16_1_8_12_1_405 49 120 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 220 4 12 30 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 220 (accept_3_3 47 120 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 220 2 23 60 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 120 220 5 9 24 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 220 4 11 30 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 220 2 21 60 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 220 (accept_3_3 41 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 220 20 2 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 120 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 120 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 220 2 19 60 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 37
  120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 220 4 9 30 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 120 220 5 7 24 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 120 220 2 17 60 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 120 220 4 8 30 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 120 220 (Polychromatic418967fa.accept_16_15_8_12_1_2737 31 120 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 220 10 3 12 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 220 (accept_3_3 29 120 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 220 4 7 30 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 220
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 120 220 2 13 60 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 120 220 5 5 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 220 4 6 30 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 120 220 (accept_3_3 23 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 220 2 11 60 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 120 220 (Polychromatic418967fa.accept_16_5_8_12_1_1766 21 120 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 220 20 1 6 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 220 2 9 60 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 120 220 (accept_3_3 17 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 220 4 4 30 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 120 220 5 3 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 120 220 2 7 60 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 120 220 (Polychromatic418967fa.accept_16_13_8_12_1_2723 13 120 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 220 4 3 30 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 220 (accept_3_3 11 120 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 220 10 1 12 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 220 4 2 30 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 120 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 220 2 3 60 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 120 220 5 1 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 120 220 4 1 30 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 220 (Polychromatic418967fa.accept_16_3_8_12_1_2736
  3 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 220 2 1 60 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 120 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 102 119 220 (Eq.refl Bool.true) (allA_of_3_1 102 119 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 103 118 220 (Eq.refl Bool.true) (allA_succ_of_gcd 102 118 220 2 51 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 118 220 (accept_3_3 101 118 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 118 220 2 50 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 118 220 (Polychromatic418967fa.accept_13_8_1_12_1_762
  99 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 118 220 2 49 59 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 118 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 97 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 118 220 2 48 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 118 220 (accept_3_3 95 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 118 220 2 47 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 118 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 118 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 118 220 2 46 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 118 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 91 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 118 220 2 45 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 118 220 (accept_3_3 89 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 118 220 2 44 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 118 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 87 118 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 118 220 2 43 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 118 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 118 220 2 42 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 118 220 (accept_3_3 83 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 118 220 2 41 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 118 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 118 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 118 220 2 40 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 118 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 118 220 2 39 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 118 220 (accept_3_3 77 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 118 220 2 38 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 118 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 118 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 118 220 2 37 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 118 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 118 220 2 36 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 118 220 (accept_3_3 71 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 118 220 2 35 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 118 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 118 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 118 220 2 34 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 118 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 118 220 2 33 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 118 220 (accept_3_3 65 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 118 220 2 32 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 118 220 (Polychromatic418967fa.accept_13_11_1_12_1_742 63 118 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 220 2 31 59 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 61 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 118 220 2 30 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 118 220 (accept_3_3 59 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 220 2 29 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 118 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 220 2 28 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 118 220 2 27 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 118 220 (accept_3_3 53 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 220 2 26 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 118 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 220 2 25 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 220 2 24 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 220 (accept_3_3 47 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 220 2 23 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 220 (Polychromatic418967fa.accept_14_3_6_10_1_752 45 118 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 220 2 22 59 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 220 2 21 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 220 (accept_3_3 41 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 220 2 20 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 118 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 220 2 19 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 220 2 18 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 220 (accept_3_3 35 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 220 2 17 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 118 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 220 2 16 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 220 2 15 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 220 (accept_3_3 29 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 220 2 14 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 220 (Polychromatic418967fa.accept_15_12_13_10_1_812 27 118 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 220 2 13 59 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 220 2 12 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 220 (accept_3_3 23 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 220 2 11 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 118 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 220 2 10 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 220 2 9 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 118 220 (accept_3_3 17 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 118 220 2 8 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 118 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 118 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 118 220 2 7 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 118 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 118 220 2 6 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 118 220 (accept_3_3 11 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 118 220 2 5 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 118 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 118 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 118 220 2 4 59 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 220 2 3 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 220 (accept_3_3 5 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  220 2 2 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 118 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 220 2 1 59 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 118 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 118 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 117 220 (Eq.refl Bool.true) (allA_succ_of_accept 103 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 117 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 102 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 117 220 (accept_3_3 101 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 117 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 117 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 99 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 220 (accept_3_3 98 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 220
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 96 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 117 220 (accept_3_3 95 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 220 (Polychromatic418967fa.accept_19_18_3_11_1_6066 94 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 93
  117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 220 (accept_3_3 92
  117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 91 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 117 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 90 117 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 220 (accept_3_3 89 117 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 117 220 (Polychromatic418967fa.accept_15_13_12_10_1_4352 88 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 220
  (Polychromatic418967fa.accept_16_7_5_12_1_4824 87 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 117 220 (accept_3_3 86 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 117 220 (Polychromatic418967fa.accept_15_9_12_10_1_809 84 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 220 (accept_3_3 83 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 220 (Polychromatic418967fa.accept_14_12_5_10_1_2130 82 117
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 220
  (Polychromatic418967fa.accept_8_1_5_4_1_388 81 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 117 220 (accept_3_3 80 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 117 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 220 (accept_3_3 77 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 220 (Polychromatic418967fa.accept_25_1_17_20_1_9567 76 117 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 220
  (Polychromatic418967fa.accept_19_18_3_11_1_6066 75 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 117 220 (accept_3_3 74 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 117 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 117 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 220 (accept_3_3 71 117 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 220
  (Polychromatic418967fa.accept_19_13_3_11_1_4706 70 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 117 220 (Polychromatic418967fa.accept_15_9_12_10_1_809 69 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 220 (accept_3_3 68 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 117 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 66 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 117 220 (accept_3_3 65 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 117 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 117 220 (Polychromatic418967fa.accept_25_13_17_20_1_13054 63 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 220 (accept_3_3 62 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 117 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 220
  (Polychromatic418967fa.accept_27_6_9_4_1_13053 60 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 117 220 (accept_3_3 59 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 117 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 117 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 220 (accept_3_3 56 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 117 220 (accept_3_3 53 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 117 220 (Polychromatic418967fa.accept_15_7_12_10_1_4335 52 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 117 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 220 (accept_3_3 50 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 220
  (Polychromatic418967fa.accept_17_14_15_16_1_1271 48 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 220 (accept_3_3 47 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 220 (Polychromatic418967fa.accept_19_8_3_11_1_6048 46 117 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 220 (Polychromatic418967fa.accept_17_11_15_16_1_4377 45
  117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 220 (accept_3_3 44
  117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 117 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 117 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 220 (accept_3_3 41 117 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 117 220 (Polychromatic418967fa.accept_14_12_5_10_1_2130 40 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 220
  (Polychromatic418967fa.accept_15_9_12_10_1_809 39 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 117 220 (accept_3_3 38 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 117 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 220 (accept_3_3 35 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 220 (Polychromatic418967fa.accept_23_11_2_13_1_11441 34 117 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 220
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 117 220 (accept_3_3 32 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 117 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 220 (accept_3_3 29 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 220 (Polychromatic418967fa.accept_15_13_12_10_1_4352 28 117 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 220
  (Polychromatic418967fa.accept_19_8_3_11_1_6048 27 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 117 220 (accept_3_3 26 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 117 220 (Polychromatic418967fa.accept_15_9_12_10_1_809 24 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 220 (accept_3_3 23 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 117 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 220
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 220 (accept_3_3 20 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 117 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 117 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 220 (accept_3_3 17 117 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 16
  117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 220 (accept_3_3 14 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 220 (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 220 (accept_3_3 11 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 220 (Polychromatic418967fa.accept_16_10_5_12_1_4925 10 117
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 220 (accept_3_3 8 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 220 (accept_3_3 5 117 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 220 (Polychromatic418967fa.accept_16_4_5_12_1_2749 4 117 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 220
  (Polychromatic418967fa.accept_21_3_12_10_1_3885 3 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 220 (accept_3_3 2 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 116 220 (Eq.refl Bool.true) (allA_of_3_1 105 116 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 106 115 220 (Eq.refl Bool.true) (allA_succ_of_gcd 105 115 220 5 21 23 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 115 220 (accept_3_3 104 115 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 115 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 103 115
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 102 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 115 220 (accept_3_3 101 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  100 115 220 5 20 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 99 115 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 115 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 115 220 (accept_3_3 98 115 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 115 220 (Polychromatic418967fa.accept_14_13_3_10_1_2159 97 115 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 115 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 96 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 95 115 220 5 19 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 94 115 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 94 115 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 115 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 115 220 (accept_3_3 92 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 115 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 115 220 5 18 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 115 220 (accept_3_3 89 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 115 220 (Polychromatic418967fa.accept_13_10_11_12_1_1320 88 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 87
  115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 115 220 (accept_3_3 86
  115 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 115 220 5 17 23 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 115 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 115 220 (accept_3_3 83 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 115 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 115 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 115 220 5 16 23 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 115 220
  (Polychromatic418967fa.accept_8_7_3_4_1_404 79 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 115 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 115 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 220 (accept_3_3 77 115 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 115 220 (Polychromatic418967fa.accept_14_6_3_10_1_3905 76 115 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 115 220 5 15 23 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 115 220 (accept_3_3 74 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 73
  115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 220
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 72 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 115 220 (accept_3_3 71 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 115 220 5 14 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 115 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 220 (accept_3_3 68 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 115 220 (Polychromatic418967fa.accept_18_13_7_4_1_2738 67 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 115 220 5 13 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 115 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 63
  115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 220 (accept_3_3 62
  115 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 220
  (Polychromatic418967fa.accept_30_1_25_10_1_13052 61 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 115 220 5 12 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 115 220 (accept_3_3 59 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 115 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 115 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 220 (accept_3_3 56 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 115 220 5 11 23 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 115 220
  (Polychromatic418967fa.accept_17_3_13_16_1_2183 54 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 115 220 (accept_3_3 53 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 115 220 (Polychromatic418967fa.accept_16_4_3_12_1_4892 52 115 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 115 220 5 10 23 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 115 220
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 49 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 115 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 220 (accept_3_3 47 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 115 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 115 220 5 9 23 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 115 220 (accept_3_3 44 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 220
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 43 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 220 (accept_3_3 41 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 115 220 5 8 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 115 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 220 (accept_3_3 38 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 37
  115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 220
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 115 220 5 7 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 115 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 115 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 220 (accept_3_3 32 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 115 220 5 6 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 115 220 (accept_3_3 29 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 115 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 115 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 220 (accept_3_3 26 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 115 220 5 5 23 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 115 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 220 (accept_3_3 23 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 115 220 5 4 23 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 115 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 220 (Polychromatic418967fa.accept_19_18_1_11_1_10478 18 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 220 (accept_3_3 17 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 220 (Polychromatic418967fa.accept_18_16_7_4_1_3901 16 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 115 220 5 3 23 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 115 220 (accept_3_3 14
  115 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 220
  (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 220 (accept_3_3 11 115 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 115 220 5 2 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 115 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 220 (accept_3_3 8 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 7
  115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 115 220 5 1 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 115 220 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 115 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 220 (accept_3_3 2 115 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 1
  115 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 114 220 (Eq.refl Bool.true) (allA_succ_of_gcd 106 114 220 2 53 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 114 220
  (Polychromatic418967fa.accept_12_9_6_4_1_402 105 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 114 220 2 52 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 114 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 103 114 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 114 220 2 51 57 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 114 220 (accept_3_3 101 114 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 114 220 2 50 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 114 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 99 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 114 220 2 49 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 114 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 114 220 2 48 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 114 220 (accept_3_3 95 114 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 220 2 47 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 114 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 93
  114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 114 220 2 46 57 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 114 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 91 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 220 2 45 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 220 (accept_3_3 89 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 114 220 2 44 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 114 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 87 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 114 220 2 43 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 114 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 85 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 220 2 42 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 220 (accept_3_3 83 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 114 220 2 41 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 114 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 114 220 2 40 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 114 220
  (Polychromatic418967fa.accept_9_7_6_4_1_483 79 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 220 2 39 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 220 (accept_3_3 77 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 114 220 2 38 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 114 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 114 220 2 37 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 73 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 220 2 36 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 220 (accept_3_3 71 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 114 220 2 35 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 114 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 114 220 2 34 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 220
  (Polychromatic418967fa.accept_13_2_10_12_1_757 67 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 220 2 33 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 220 (accept_3_3 65 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 114 220 2 32 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 114 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 114 220 2 31 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 61 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 220 2 30 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 220 (accept_3_3 59 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 114 220 2 29 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 114 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 114 220 2 28 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 220 2 27 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 220 (accept_3_3 53 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 114 220 2 26 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 114 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 114 220 2 25 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 220
  (Polychromatic418967fa.accept_15_4_9_10_1_5384 49 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 220 2 24 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 220 (accept_3_3 47 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 114 220 2 23 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 114 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 114 220 2 22 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 220 2 21 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 220 (accept_3_3 41 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 114 220 2 20 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 114 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 114 220 2 19 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 220 2 18 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 220 (accept_3_3 35 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 220 2 17 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 114 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 114 220 2 16 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 220
  (Polychromatic418967fa.accept_15_1_9_10_1_2327 31 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 220 2 15 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 220 (accept_3_3 29 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 220 2 14 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 220 2 13 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 220
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 220 2 12 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 220 (accept_3_3 23 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 220 2 11 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 220 2 10 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 220 2 9 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 220 (accept_3_3 17 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 114 220 2 8 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 114 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 220 2 7 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 220 2 6 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 220 (accept_3_3 11 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 220 2 5 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 114 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 114 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 220 2 4 57 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 220
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 220 2 3 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 220 (accept_3_3 5 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114
  220 2 2 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  114 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 114 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 114 220 2 1 57 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 114 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 114 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 113 220 (Eq.refl Bool.true) (allA_of_3_1 108 113 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 109 112 220 (Eq.refl Bool.true) (allA_succ_of_gcd 108 112 220 4 27 28 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 112 220 (accept_3_3 107 112 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 112 220 2 53 56 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 112 220
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 105 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 112 220 4 26 28 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 112 220 (Polychromatic418967fa.accept_19_8_17_11_1_3406 103 112 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 112 220 2 51 56 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 112 220 (accept_3_3
  101 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 112 220 4 25 28 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 112 220
  (Polychromatic418967fa.accept_19_4_17_11_1_7527 99 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 112 220 2 49 56 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 112 220 (Polychromatic418967fa.accept_21_13_7_10_1_8599 97 112 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 112 220 4 24 28 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 112 220 (accept_3_3 95
  112 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 112 220 2 47 56 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 112 220
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 93 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 112 220 4 23 28 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 112 220 (Polychromatic418967fa.accept_15_1_7_10_1_287 91 112 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 112 220 2 45 56 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 112 220 (accept_3_3 89 112 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 112 220 4 22 28 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 112 220
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 87 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 112 220 2 43 56 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 112 220 (Polychromatic418967fa.accept_13_7_8_12_1_2810 85 112 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 112 220 4 21 28 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 112 220 (accept_3_3 83 112 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 112 220 2 41 56 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 112 220
  (Polychromatic418967fa.accept_19_5_17_11_1_2225 81 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 112 220 4 20 28 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 112 220 (Polychromatic418967fa.accept_13_1_8_12_1_2045 79 112 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 112 220 2 39 56 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 112 220 (accept_3_3 77 112 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 112 220 4 19 28 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 112 220
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 75 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 112 220 2 37 56 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 112 220 (Polychromatic418967fa.accept_23_4_20_13_1_13051 73 112 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 112 220 4 18 28 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 112 220 (accept_3_3 71
  112 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 112 220 2 35 56 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 112 220
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 69 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 112 220 4 17 28 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 112 220 (Polychromatic418967fa.accept_25_17_12_20_1_13050 67 112 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 112 220 2 33 56 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 112 220 (accept_3_3 65 112 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 112 220 4 16 28 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 112 220
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 63 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 112 220 2 31 56 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 112 220 (Polychromatic418967fa.accept_13_9_8_12_1_2031 61 112 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 112 220 4 15 28 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 112 220 (accept_3_3 59 112 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 112 220 2 29 56 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 112 220
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 57 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 112 220 4 14 28 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 112 220 (Polychromatic418967fa.accept_21_13_7_10_1_8599 55 112 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 112 220 2 27 56 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 112 220 (accept_3_3 53 112 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 112 220 4 13 28 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 112 220
  (Polychromatic418967fa.accept_19_13_17_11_1_4716 51 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 112 220 2 25 56 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 112 220 (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 112 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 112 220 4 12 28 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 112 220 (accept_3_3 47
  112 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 112 220 2 23 56 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 112 220
  (Polychromatic418967fa.accept_21_3_7_10_1_7002 45 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 112 220 4 11 28 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 112 220 (Polychromatic418967fa.accept_13_4_8_12_1_3526 43 112 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 112 220 2 21 56 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 112 220 (accept_3_3 41 112 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 112 220 4 10 28 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 112 220
  (Polychromatic418967fa.accept_21_18_7_10_1_13049 39 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 112 220 2 19 56 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 112 220 (Polychromatic418967fa.accept_19_18_17_11_1_9064 37 112 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 112 220 4 9 28 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 112 220 (accept_3_3 35
  112 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 112 220 2 17 56 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 112 220
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 112 220 4 8 28 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 112 220 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 112 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 220 2 15 56 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 220 (accept_3_3 29 112 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 220 4 7 28 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 220 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 112
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 220 2 13 56 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 220
  (Polychromatic418967fa.accept_19_6_17_11_1_6039 25 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 112 220 4 6 28 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 112 220 (accept_3_3 23 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 220 2 11 56 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 220 (Polychromatic418967fa.accept_24_21_16_4_1_13048 21 112 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 220 4 5 28 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 220
  (Polychromatic418967fa.accept_15_4_7_10_1_807 19 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 220 2 9 56 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 112 220 (accept_3_3 17 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 112 220 4 4 28 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 112 220 (Polychromatic418967fa.accept_21_15_7_10_1_8610 15 112 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 112 220 2 7 56 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 112 220
  (Polychromatic418967fa.accept_19_13_17_11_1_4716 13 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 112 220 4 3 28 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 112 220 (accept_3_3 11 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 112 220 2 5 56 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 112 220 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 112 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 220 4 2 28 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 112 220 (Polychromatic418967fa.accept_13_7_8_12_1_2810
  7 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 220 2 3 56 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 220 (accept_3_3 5
  112 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112 220 4 1 28 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 112 220
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 3 112 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 112 220 2 1 56 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 112 220 (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 112 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 112
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 111 220 (Eq.refl Bool.true) (allA_succ_of_accept 109 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  109 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 220
  (Polychromatic418967fa.accept_13_4_7_12_1_2823 108 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 111 220 (accept_3_3 107 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 106 111 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 111 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 105 111
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 220 (accept_3_3 104 111
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 103 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 111 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 102 111 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 220 (accept_3_3 101 111 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 111 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 100 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 111 220
  (Polychromatic418967fa.accept_8_3_7_4_1_42 99 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 111 220 (accept_3_3 98 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 111 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 96 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 220 (accept_3_3 95 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 111 220 (Polychromatic418967fa.accept_15_4_6_10_1_823 94 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 111 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 93 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 111 220 (accept_3_3 92 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 111 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 90 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 220 (accept_3_3 89 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 111 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 111 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 111 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 111 220 (accept_3_3 86 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 111 220 (Polychromatic418967fa.accept_13_6_7_12_1_3504 84 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 220 (accept_3_3 83 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 111 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 111 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 81 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 111 220 (accept_3_3 80 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 111 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 220 (accept_3_3 77 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 220 (Polychromatic418967fa.accept_13_11_7_12_1_2758 76 111 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 111 220
  (Polychromatic418967fa.accept_8_3_7_4_1_42 75 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 111 220 (accept_3_3 74 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 111 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 220 (accept_3_3 71 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 111 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 111 220 (accept_3_3 68 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 111 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 66 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 220 (accept_3_3 65 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 111 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 111 220
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 220 (accept_3_3 62 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 111 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 111 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 220 (accept_3_3 59 111 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 220 (Polychromatic418967fa.accept_7_2_6_3_1_100
  58 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 220
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 57 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 111 220 (accept_3_3 56 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 111 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 220 (accept_3_3 53 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 111 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 111 220 (accept_3_3 50 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 111 220 (Polychromatic418967fa.accept_15_3_6_10_1_1539 48 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 220 (accept_3_3 47 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 111 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 220
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 111 220 (accept_3_3 44 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 111 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 220 (accept_3_3 41 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 220 (Polychromatic418967fa.accept_16_8_15_12_1_1747 40 111 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 111 220 (accept_3_3 38 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 111 220 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 220 (accept_3_3 35 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 111 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 111 220 (accept_3_3 32 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 111 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 220 (accept_3_3 29 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 220
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 111 220 (accept_3_3 26 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 111 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 220 (accept_3_3 23 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 220 (Polychromatic418967fa.accept_25_22_11_20_1_13047 22 111 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 220
  (Polychromatic418967fa.accept_13_8_7_12_1_3637 21 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 220 (accept_3_3 20 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 220 (accept_3_3 17 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 220 (accept_3_3 14 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 111 220 (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 220 (accept_3_3 11 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 111 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 111 220 (accept_3_3 8 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 111 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 220 (accept_3_3 5 111 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 111 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 220
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 220 (accept_3_3 2 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 111 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 220 (allA_of_3_1 110 110 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 220
  (allA_succ_of_accept 108 109 220 (Polychromatic418967fa.accept_13_4_5_12_1_751 108 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 220 (accept_3_3 107 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 106 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 220 (accept_3_3 104 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 220 (Polychromatic418967fa.accept_15_13_4_10_1_821 103 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 109 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 102 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 220 (accept_3_3 101 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 220 (Polychromatic418967fa.accept_16_4_13_12_1_1740 100
  109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 220 (accept_3_3 98 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 220 (accept_3_3 95 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 94 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 220 (accept_3_3 92 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 220 (Polychromatic418967fa.accept_14_7_11_10_1_2155 91 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 220 (accept_3_3 89 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 220 (accept_3_3 86 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 220 (accept_3_3 83 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 220 (accept_3_3 80 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 220 (accept_3_3 77 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 220 (accept_3_3 74 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 73 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 220 (Polychromatic418967fa.accept_13_7_5_12_1_1305 72 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 220 (accept_3_3 71 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 109 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 220 (accept_3_3 68 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 220 (Polychromatic418967fa.accept_13_2_5_12_1_2043 67 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 220 (accept_3_3 65 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 220 (accept_3_3 62 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 220 (accept_3_3 59 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 220 (accept_3_3 56 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 220 (Polychromatic418967fa.accept_13_2_5_12_1_2043 54 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 220 (accept_3_3 53 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 109 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 220 (accept_3_3 50 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 220 (accept_3_3 47 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 220 (accept_3_3 44 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 220 (accept_3_3 41 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 220 (Polychromatic418967fa.accept_13_1_5_12_1_306 40 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 220 (accept_3_3 38 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 220 (Polychromatic418967fa.accept_15_7_4_10_1_1513 37 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 220 (accept_3_3 35 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 220 (accept_3_3 32 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 220 (Polychromatic418967fa.accept_16_15_13_12_1_1787 31 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 220 (accept_3_3 29 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 220 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 109
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 220 (accept_3_3 26 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 220 (accept_3_3 23 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 220 (accept_3_3 20 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 220 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 220 (Polychromatic418967fa.accept_26_18_5_12_1_13046 18 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 220 (accept_3_3 17 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 109 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 220 (accept_3_3 14 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 220 (accept_3_3 11 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 220 (accept_3_3 8 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 220 (accept_3_3 5 109 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 220 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 109 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 220 (accept_3_3 2 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 109 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 220 (allA_succ_of_accept 107 108 220 (accept_3_3 107 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 108 220 2 53 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 108 220 (Polychromatic418967fa.accept_25_5_8_20_1_11333 105 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 108 220 4 26 27 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 108 220
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 103 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 108 220 2 51 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 108 220 (accept_3_3 101 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 108 220 4 25 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 108 220 (Polychromatic418967fa.accept_13_8_4_12_1_2753 99 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 108 220 2 49 54 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 108 220
  (Polychromatic418967fa.accept_15_7_3_10_1_817 97 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 220 4 24 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 220 (accept_3_3 95 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 108 220 2 47 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 108 220 (Polychromatic418967fa.accept_13_2_4_12_1_745 93 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 108 220 4 23 27 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 220
  (Polychromatic418967fa.accept_21_7_3_10_1_13044 91 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 108 220 2 45 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 108 220 (accept_3_3 89 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 108 220 4 22 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 108 220 (Polychromatic418967fa.accept_23_18_16_13_1_13045 87 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 108 220 2 43 54 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 220
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 85 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 220 4 21 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 220 (accept_3_3 83 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 108 220 2 41 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 108 220 (Polychromatic418967fa.accept_13_3_4_12_1_36 81 108 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 108 220 4 20 27 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 220
  (Polychromatic418967fa.accept_19_3_13_11_1_2220 79 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 108 220 2 39 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 108 220 (accept_3_3 77 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 108 220 4 19 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 108 220 (Polychromatic418967fa.accept_17_7_6_16_1_2195 75 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 108 220 2 37 54 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 220
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 73 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 220 4 18 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 220 (accept_3_3 71 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 108 220 2 35 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 108 220 (Polychromatic418967fa.accept_15_9_3_10_1_2312 69 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 108 220 4 17 27 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 220
  (Polychromatic418967fa.accept_13_2_4_12_1_745 67 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 220 2 33 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 220 (accept_3_3 65 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 108 220 4 16 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 108 220 (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 108 220 2 31 54 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 220
  (Polychromatic418967fa.accept_17_10_6_16_1_6862 61 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 108 220 4 15 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 108 220 (accept_3_3 59 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 108 220 2 29 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 108 220 (Polychromatic418967fa.accept_13_5_4_12_1_2058 57 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 108 220 4 14 27 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 220
  (Polychromatic418967fa.accept_13_3_4_12_1_36 55 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 220 2 27 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 220 (accept_3_3 53 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 108 220 4 13 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 108 220 (Polychromatic418967fa.accept_15_6_3_10_1_2341 51 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 220 2 25 54 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 220
  (Polychromatic418967fa.accept_21_7_3_10_1_13044 49 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 108 220 4 12 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 108 220 (accept_3_3 47 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 108 220 2 23 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 220 (Polychromatic418967fa.accept_19_7_13_11_1_1208 45 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 220 4 11 27 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 220
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 43 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 108 220 2 21 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 108 220 (accept_3_3 41 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 220 4 10 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 220 (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 220 2 19 54 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 220
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 37 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 108 220 4 9 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 108 220 (accept_3_3 35 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 108 220 2 17 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 108 220 (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 220 4 8 27 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 220
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 220 2 15 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 220 (accept_3_3 29 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 220 4 7 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 108 220 (Polychromatic418967fa.accept_17_10_6_16_1_6862 27 108 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 220 2 13 54 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 220
  (Polychromatic418967fa.accept_19_6_13_11_1_7495 25 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 108 220 4 6 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 108 220 (accept_3_3 23 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 108 220 2 11 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 108 220 (Polychromatic418967fa.accept_13_8_4_12_1_2753 21 108 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 220 4 5 27 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 220
  (Polychromatic418967fa.accept_24_19_12_4_1_13043 19 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 108 220 2 9 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 108 220 (accept_3_3 17 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 108 220 4 4 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 108 220 (Polychromatic418967fa.accept_13_2_4_12_1_745 15 108 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 220 2 7 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 220
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 108 220 4 3 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 108 220 (accept_3_3 11 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 220 2 5 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 108 220 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 108 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 220 4 2 27 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 220 (Polychromatic418967fa.accept_13_7_4_12_1_1341
  7 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 220 2 3 54 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 220 (accept_3_3 5
  108 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 220 4 1 27 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 220
  (Polychromatic418967fa.accept_13_3_4_12_1_36 3 108 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 108 220 2 1 54 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 220 (Polychromatic418967fa.accept_21_1_3_10_1_5401 1 108 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 220 (allA_of_3_1 107 107 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 220
  (allA_succ_of_accept 105 106 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 105 106 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 106 220 2 52 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 106 220 (Polychromatic418967fa.accept_7_5_1_3_1_103
  103 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 106 220 2 51 53 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 106 220
  (accept_3_3 101 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 106 220 2 50 53 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 106 220
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 99 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 106 220 2 49 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 106 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 97 106 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 106 220 2 48 53 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 106 220 (accept_3_3 95 106 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 106 220 2 47 53 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 106 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 106 220 2 46 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 106 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 106 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 106 220 2 45 53 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 106 220 (accept_3_3 89 106 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 106 220 2 44 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 106 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 87
  106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 106 220 2 43 53 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 106 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 106 220 2 42 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 106 220 (accept_3_3 83 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 106 220 2 41 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 106 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 106 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 106 220 2 40 53 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 106 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 79 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 106 220 2 39 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 106 220 (accept_3_3 77 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 106 220 2 38 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 106 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 106 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 220 2 37 53 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 73 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 220 2 36 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 220 (accept_3_3 71 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 220 2 35 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 106 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 220 2 34 53 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 67 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 106 220 2 33 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 220 (accept_3_3 65 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 220 2 32 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 220 (Polychromatic418967fa.accept_25_13_6_20_1_9559 63 106 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 220 2 31 53 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 220 2 30 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 220 (accept_3_3 59 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 220 2 29 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 106 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 220 2 28 53 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 55 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 220 2 27 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 220 (accept_3_3 53 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 220 2 26 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 106 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 220 2 25 53 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 220 2 24 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 220 (accept_3_3 47 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 220 2 23 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 220 (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 106 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 220 2 22 53 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 220 2 21 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 220 (accept_3_3 41 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 220 2 20 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 106 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 220 2 19 53 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 220 2 18 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 220 (accept_3_3 35 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 220 2 17 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 106 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 220 2 16 53 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 220 2 15 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 220 (accept_3_3 29 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 220 2 14 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 220 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 106 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 220 2 13 53 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 220 2 12 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 220 (accept_3_3 23 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 220 2 11 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 106 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 220 2 10 53 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 220 2 9 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 106 220 (accept_3_3 17 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 106 220 2 8 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 106 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 106 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 220 2 7 53 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 106 220 2 6 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 106 220 (accept_3_3 11 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 106 220 2 5 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 106 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 106 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 220 2 4 53 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 106 220 2 3 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 220 (accept_3_3 5 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  220 2 2 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 106 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 220 2 1 53 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 106 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 106 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 220 (allA_succ_of_accept 104 105 220 (accept_3_3 104 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 102 105
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 220 (accept_3_3 101 105
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 105 220 5 20 21 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 105 220
  (Polychromatic418967fa.accept_13_8_1_12_1_762 99 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 105 220 (accept_3_3 98 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 105 220 (Polychromatic418967fa.accept_13_5_1_12_1_740 96 105 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 105 220 5 19 21 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 105 220
  (Polychromatic418967fa.accept_19_18_10_11_1_6058 94 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 105 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 93 105 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 220 (accept_3_3 92 105 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 105 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 105 220 5 18 21 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 105 220 (accept_3_3 89 105 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 220 (Polychromatic418967fa.accept_9_7_6_4_1_483
  88 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 105 220
  (Polychromatic418967fa.accept_14_3_7_10_1_2146 87 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 105 220 (accept_3_3 86 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  105 220 5 17 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 105 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 220 (accept_3_3 83 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 105 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 105 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 105 220
  (Polychromatic418967fa.accept_14_11_7_10_1_4852 81 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 105 220 5 16 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 105 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 78 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 105 220 (accept_3_3 77 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 105 220 (Polychromatic418967fa.accept_13_11_1_12_1_742 76 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 105 220 5 15 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 105 220 (accept_3_3 74 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 220 (Polychromatic418967fa.accept_16_8_9_12_1_1737 72 105
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 220 (accept_3_3 71 105
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 220 5 14 21 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 105 220
  (Polychromatic418967fa.accept_8_5_1_4_1_628 69 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 105 220 (accept_3_3 68 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 105 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 105 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 105 220 5 13 21 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 105 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 64 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 105 220 (Polychromatic418967fa.accept_13_11_1_12_1_742 63 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 220 (accept_3_3 62 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 105 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 220 5 12 21 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 220 (accept_3_3 59 105 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 220 (Polychromatic418967fa.accept_17_7_3_16_1_2208 58 105
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 105 220 (accept_3_3 56 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  105 220 5 11 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 105 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 220 (accept_3_3 53 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 105 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 105 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 220
  (Polychromatic418967fa.accept_16_3_9_12_1_4831 51 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 105 220 5 10 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 105 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 220 (Polychromatic418967fa.accept_9_3_6_4_1_210
  48 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 220 (accept_3_3 47
  105 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 46 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 105 220 5 9 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 105 220 (accept_3_3 44 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 105 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 105 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 220 (accept_3_3 41 105 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 220 5 8 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 105 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 105 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 220 (accept_3_3 38 105 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37
  105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 220
  (Polychromatic418967fa.accept_16_4_9_12_1_4829 36 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 105 220 5 7 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 105 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 220 (Polychromatic418967fa.accept_25_8_5_20_1_13042 33 105
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 220 (accept_3_3 32 105
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 220 5 6 21 44
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 220
  (accept_3_3 29 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 28 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 105 220 (Polychromatic418967fa.accept_18_9_15_4_1_5173 27 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 220 (accept_3_3 26 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 105 220 5 5 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 105 220 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 105 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 220 (accept_3_3 23 105 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 220 (Polychromatic418967fa.accept_19_3_10_11_1_7669 22 105
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 220
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 105 220 5 4 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 105 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 220 (accept_3_3 17 105 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 220 (Polychromatic418967fa.accept_9_7_6_4_1_483
  16 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 220 5 3 21 44
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 220
  (accept_3_3 14 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 220 (accept_3_3 11 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 105 220 5 2 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 105 220 (Polychromatic418967fa.accept_18_9_15_4_1_5173 9 105 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 220 (accept_3_3 8 105 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 105 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 105 220 5 1 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 105 220 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 105 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 105 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 220 (accept_3_3 2 105 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  105 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 220 (allA_of_3_1 104 104 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 220
  (allA_succ_of_accept 102 103 220 (Polychromatic418967fa.accept_15_12_13_10_1_812 102 103 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 220 (accept_3_3 101 103 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 103 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 220 (accept_3_3 98 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 220 (Polychromatic418967fa.accept_17_12_1_16_1_4360 97 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 220 (Polychromatic418967fa.accept_14_12_5_10_1_2130 96 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 220 (accept_3_3 95 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 94 103
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 220 (accept_3_3 92 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 91 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 220 (Polychromatic418967fa.accept_17_5_1_16_1_4359 90 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 220 (accept_3_3 89 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 220 (Polychromatic418967fa.accept_16_8_7_12_1_7207 88 103
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 220 (accept_3_3 86 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 220 (Polychromatic418967fa.accept_16_4_7_12_1_2734 84 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 220 (accept_3_3 83 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 82 103
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 220 (accept_3_3 80 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 103 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 220 (accept_3_3 77 103 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 220 (Polychromatic418967fa.accept_15_1_13_10_1_1507 76 103 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 220 (accept_3_3 74 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 220 (Polychromatic418967fa.accept_17_5_1_16_1_4359 73 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 103 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 220 (accept_3_3 71 103 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 220 (accept_3_3 68 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 220 (Polychromatic418967fa.accept_16_2_7_12_1_3793 66 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 220 (accept_3_3 65 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 103 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 220 (accept_3_3 62 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 220 (Polychromatic418967fa.accept_15_1_13_10_1_1507 61 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 220 (Polychromatic418967fa.accept_19_3_8_11_1_7609 60 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 220 (accept_3_3 59 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 103 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 220 (accept_3_3 56 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 220 (Polychromatic418967fa.accept_19_17_8_11_1_7605 55 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 220 (Polychromatic418967fa.accept_14_12_5_10_1_2130 54 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 220 (accept_3_3 53 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 220 (Polychromatic418967fa.accept_16_4_7_12_1_2734 52 103
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 220 (accept_3_3 50 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 220 (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 220 (Polychromatic418967fa.accept_15_3_13_10_1_2332 48 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 220 (accept_3_3 47 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 103
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 220 (accept_3_3 44 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 220 (Polychromatic418967fa.accept_15_12_13_10_1_812 42 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 220 (accept_3_3 41 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 220 (Polychromatic418967fa.accept_14_12_5_10_1_2130 40 103
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 220 (accept_3_3 38 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 103 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 220 (accept_3_3 35 103 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 220 (accept_3_3 32 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 220 (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 103 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 220 (accept_3_3 29 103 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 220 (Polychromatic418967fa.accept_18_10_13_4_1_5153 28 103 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 220 (accept_3_3 26 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 220 (Polychromatic418967fa.accept_18_7_13_4_1_1670 25 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 220 (Polychromatic418967fa.accept_16_8_7_12_1_7207 24 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 220 (accept_3_3 23 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 103 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 220 (accept_3_3 20 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 220 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 220 (accept_3_3 17 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 103 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 220 (accept_3_3 14 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 220 (Polychromatic418967fa.accept_26_13_25_12_1_13041 13 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 220 (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 103 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 220 (accept_3_3 11 103 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 220 (Polychromatic418967fa.accept_12_10_7_4_1_820
  10 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 220 (accept_3_3 8 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 220 (Polychromatic418967fa.accept_18_7_13_4_1_1670 7 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 220 (Polychromatic418967fa.accept_25_6_3_20_1_13033 6 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 220 (accept_3_3 5 103 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 220 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 103
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 220 (accept_3_3 2 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 103 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 220 (allA_succ_of_accept 101 102 220 (accept_3_3 101 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 102 220 2 50 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 102 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 99 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 220 2 49 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 97 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 102 220 2 48 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 102 220 (accept_3_3 95 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 220 2 47 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 93 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 220 2 46 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 91 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 220 2 45 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 220 (accept_3_3 89 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 102 220 2 44 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 102 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 102 220 2 43 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 85 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 220 2 42 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 220 (accept_3_3 83 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 102 220 2 41 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 102 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 102 220 2 40 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 79 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 220 2 39 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 220 (accept_3_3 77 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 102 220 2 38 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 102 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 75 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 102 220 2 37 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 73 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 220 2 36 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 220 (accept_3_3 71 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 102 220 2 35 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 102 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 102 220 2 34 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 220
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 67 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 102 220 2 33 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 102 220 (accept_3_3 65 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 102 220 2 32 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 102 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 102 220 2 31 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 61 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 220 2 30 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 220 (accept_3_3 59 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 102 220 2 29 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 102 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 220 2 28 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 220 2 27 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 220 (accept_3_3 53 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 220 2 26 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 102 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 220 2 25 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 220
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 49 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 102 220 2 24 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 102 220 (accept_3_3 47 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 220 2 23 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 220 2 22 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 220 2 21 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 220 (accept_3_3 41 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 102 220 2 20 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 220 2 19 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 220 2 18 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 220 (accept_3_3 35 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 220 2 17 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 220 2 16 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 220
  (Polychromatic418967fa.accept_19_12_7_11_1_7658 31 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 102 220 2 15 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 102 220 (accept_3_3 29 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 220 2 14 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 220 2 13 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 220 2 12 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 220 (accept_3_3 23 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 220 2 11 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 220 2 10 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 220 2 9 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 220 (accept_3_3 17 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 102 220 2 8 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 102 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 220 2 7 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 220 2 6 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 220 (accept_3_3 11 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 220 2 5 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 102 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 102 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 220 2 4 51 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 220 2 3 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 220 (accept_3_3 5 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102
  220 2 2 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  102 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 102 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 102 220 2 1 51 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 102 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 102 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 220 (allA_of_3_1 101 101 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 220 (allA_succ_of_accept 99
  100 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 99 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 100 220 2 49 50 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 100 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 100 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 100 220 4 24 25 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 100 220 5 19 20 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 100 220 2 47 50 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 100 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 93 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 100 220 4 23 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 100 220 (Polychromatic418967fa.accept_16_11_4_12_1_1760 91 100 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 100 220 10 9 10 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 100 220 (accept_3_3 89 100 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 100 220 4 22 25 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 100 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 87 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 100 220 2 43 50 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 100 220 5 17 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 100 220 4 21 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 100 220 (accept_3_3 83 100 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 100 220 2 41 50 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 100 220 (Polychromatic418967fa.accept_13_3_9_12_1_2062 81 100 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 100 220 20 4 5 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 100 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 79 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 100 220 2 39 50 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 100 220 (accept_3_3 77 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 100 220 4 19 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 100 220 5 15 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 100 220 2 37 50 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 100 220 (Polychromatic418967fa.accept_13_8_9_12_1_2813 73 100
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 100 220 4 18 25 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 100 220 (accept_3_3 71
  100 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 100 220 10 7 10 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 100 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 100 220 4 17 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 100 220 (Polychromatic418967fa.accept_16_3_4_12_1_3799 67 100 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 100 220 2 33 50 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 100 220 5 13 20 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 100 220 4 16 25 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 100 220
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 100 220 2 31 50 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 100 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 100 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 100 220 20 3 5 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 100 220 (accept_3_3 59 100 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 100 220 2 29 50 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 100 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 100 220 4 14 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 100 220 5 11 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 100 220 2 27 50 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 100 220 (accept_3_3 53 100 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 100 220 4 13 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 100 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 100 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 220 10 5 10 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 220
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 49 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 100 220 4 12 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 100 220 (accept_3_3 47 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 220 2 23 50 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 100 220 5 9 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 100 220 4 11 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 100 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 100 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 100 220 2 21 50 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 100 220 (accept_3_3 41 100 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 100 220 20 2 5 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 100 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 100 220 2 19 50 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 100 220 (Polychromatic418967fa.accept_16_5_4_12_1_3800 37 100 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 100 220 4 9 25 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 100 220 5 7 20 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 100 220 2 17 50 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 100 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 100 220 4 8 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 100 220 (Polychromatic418967fa.accept_16_15_4_12_1_2731 31 100 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 220 10 3 10 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 220 (accept_3_3 29 100 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 220 4 7 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 27
  100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 220 2 13 50 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 100 220 5 5 20 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 100 220 4 6 25 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 220 (accept_3_3 23
  100 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 220 2 11 50 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 220 20 1 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 100 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 100 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 220 2 9 50 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 220 (accept_3_3 17 100 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 220 4 4 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 100 220 5 3 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 100 220 2 7 50 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 220 4 3 25 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 220 (accept_3_3 11
  100 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 220 10 1 10 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 220
  (Polychromatic418967fa.accept_16_9_4_12_1_4896 9 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 220 4 2 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 100 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 220 2 3 50 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 100 220 5 1 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 100 220 4 1 25 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 100 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 220 2 1 50 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 100 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 100 220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 99 220 (allA_succ_of_accept 98 99 220 (accept_3_3 98 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 99 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 99 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 220 (accept_3_3 95 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 220 (Polychromatic418967fa.accept_15_4_9_10_1_5384
  94 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 220 (accept_3_3 92 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 90 99 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 220 (accept_3_3 89 99 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 88 99 220 11 8 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 99 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 99 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 220 (accept_3_3 86 99 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 99 220
  (Polychromatic418967fa.accept_16_4_3_12_1_4892 84 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 99 220 (accept_3_3 83 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  99 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 99 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 99 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 220 (accept_3_3 80 99 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 99 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 99 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 78 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 99 220 11 7 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 76 99 220 (Polychromatic418967fa.accept_15_1_9_10_1_2327 76 99 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 220 (accept_3_3 74 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73
  99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 99 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 99 220 (accept_3_3 71 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  99 220 (Polychromatic418967fa.accept_13_5_8_12_1_2759 70 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 99 220 (Polychromatic418967fa.accept_13_4_8_12_1_3526 69 99 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 220 (accept_3_3 68 99 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 220 11 6 9 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 220 (accept_3_3 65 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 220 (Polychromatic418967fa.accept_15_4_9_10_1_5384
  64 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 220
  (Polychromatic418967fa.accept_8_7_3_4_1_404 63 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 220 (accept_3_3 62 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 99 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 220 (accept_3_3 59 99 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 99 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 220
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 57 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 220 (accept_3_3 56 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 99
  220 11 5 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  99 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 220 (accept_3_3 53 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 99 220 (Polychromatic418967fa.accept_16_4_3_12_1_4892 52 99 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 220 (accept_3_3 50 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49
  99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 220
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 48 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 99 220 (accept_3_3 47 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  99 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 99 220 (Polychromatic418967fa.accept_17_11_14_16_1_1270 45 99 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 99 220 11 4 9 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 99 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 99 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 99 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 220 (accept_3_3 41 99 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 99 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 99 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 39
  99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 220 (accept_3_3 38 99
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  37 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 220
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 99 220 (accept_3_3 35 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  99 220 (Polychromatic418967fa.accept_15_4_9_10_1_5384 34 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 99 220 11 3 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 99 220 (accept_3_3 32 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 220 (accept_3_3 29 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 220
  (Polychromatic418967fa.accept_17_11_14_16_1_1270 28 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 99 220 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 99 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 220 (accept_3_3 26 99 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 220
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 24 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 99 220 (accept_3_3 23 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 99
  220 11 2 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  99 220 (Polychromatic418967fa.accept_19_2_4_11_1_7507 21 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 220 (accept_3_3 20 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 220 (accept_3_3 17 99 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 16
  99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 220
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 220 (accept_3_3 14 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 99 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 99 220 11 1 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 99 220 (Polychromatic418967fa.accept_13_10_8_12_1_2032
  10 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 220 (accept_3_3 8 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 99 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 99 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 220 (accept_3_3 5 99 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 99 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 99 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 220 (Polychromatic418967fa.accept_15_3_9_10_1_2325
  3 99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 220 (accept_3_3 2 99
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  99 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  220 (allA_of_3_1 98 98 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 220 (allA_succ_of_accept 96 97 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 96 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 220 (accept_3_3 95 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 94 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 220 (accept_3_3 92 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 220
  (Polychromatic418967fa.accept_23_21_5_13_1_13040 90 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 97 220 (accept_3_3 89 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 97 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 97 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 97 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 220 (accept_3_3 86 97 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 85
  97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 220 (accept_3_3 83 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 220 (accept_3_3 80 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 220 (accept_3_3 77 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 220 (Polychromatic418967fa.accept_15_1_7_10_1_287 76 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 220 (accept_3_3 74 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 220 (accept_3_3 71 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 220 (accept_3_3 68 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 220 (accept_3_3 65 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 220 (accept_3_3 62 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 220 (accept_3_3 59 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 220 (accept_3_3 56 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 220
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 54 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 220 (accept_3_3 53 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 220 (Polychromatic418967fa.accept_16_4_1_12_1_1792 52 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 220 (accept_3_3 50 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 220 (Polychromatic418967fa.accept_13_10_6_12_1_2780 49 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 220 (accept_3_3 47 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 220 (accept_3_3 44 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 220 (Polychromatic418967fa.accept_16_11_1_12_1_1795 43 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 220 (accept_3_3 41 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 220 (Polychromatic418967fa.accept_16_8_1_12_1_984 40 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 220 (accept_3_3 38 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 220
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 220 (accept_3_3 35 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 220 (accept_3_3 32 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 220 (Polychromatic418967fa.accept_13_5_6_12_1_2750 31 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 220 (accept_3_3 29 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 220 (accept_3_3 26 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 220 (accept_3_3 23 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 220 (accept_3_3 20 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 220 (accept_3_3 17 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 220 (accept_3_3 14 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 220 (accept_3_3 11 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 220 (accept_3_3 8 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 220 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 97 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 220 (accept_3_3 5 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  220 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 97 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 97 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 220 (accept_3_3 2 97 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 97 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 220
  (allA_succ_of_accept 95 96 220 (accept_3_3 95 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 96
  220 2 47 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  93 96 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 96 220 4 23 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 96 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 96 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 220 2 45 48 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 220 (accept_3_3 89 96 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 220 4 22 24 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 220
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 87 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 220 2 43 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 96 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 220 4 21 24 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 220 (accept_3_3 83 96 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 220 2 41 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 220
  (Polychromatic418967fa.accept_28_25_12_24_1_13039 81 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 96 220 4 20 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 96 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 96 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 220 2 39 48 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 220 (accept_3_3 77 96 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 96 220 4 19 24 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 96 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 96 220 2 37 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 96 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 96 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 220 4 18 24 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 220 (accept_3_3 71 96 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 220 2 35 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 220 (Polychromatic418967fa.accept_13_4_5_12_1_751
  69 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 96 220 4 17 24 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 96 220
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 67 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 220 2 33 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 96 220 (accept_3_3 65 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 96 220 4 16 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 96 220 (Polychromatic418967fa.accept_15_3_6_10_1_1539 63 96 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 220 2 31 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 61
  96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 220 4 15 24 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 220 (accept_3_3 59
  96 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 220 2 29 48 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 96 220 4 14 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 96 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 96 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 220 2 27 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 220 (accept_3_3 53 96 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 220 4 13 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 96 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 220 2 25 48 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 220
  (Polychromatic418967fa.accept_15_4_6_10_1_823 49 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 220 4 12 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 220 (accept_3_3 47 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96
  220 2 23 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 96 220 (Polychromatic418967fa.accept_13_6_5_12_1_307 45 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 96 220 4 11 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 96 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 96 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 220 2 21 48 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 220 (accept_3_3 41 96 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 220 4 10 24 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 96 220 2 19 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 96 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 96 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 220 4 9 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 220 (accept_3_3 35 96 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 220 2 17 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 220 (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 96 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 96 220 4 8 24 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 220
  (Polychromatic418967fa.accept_15_1_6_10_1_23 31 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 220 2 15 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 96 220 (accept_3_3 29 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 96 220 4 7 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 96 220 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 96 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 220 2 13 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 25
  96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 220 4 6 24 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 220 (accept_3_3 23
  96 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 220 2 11 48 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 220 4 5 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 220 2 9 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 220 (accept_3_3 17 96 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 220 4 4 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 96 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 220 2 7 48 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 220
  (Polychromatic418967fa.accept_25_13_21_20_1_11319 13 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 96 220 4 3 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 96 220 (accept_3_3 11 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 96 220 2 5 48 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 96 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 220 4 2 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 220 2 3 48 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 220 (accept_3_3 5 96 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 220 4 1 24 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 96
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 220 2 1 48 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 96 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 95 220 (allA_of_3_1 95 95 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 220
  (allA_succ_of_accept 93 94 220 (Polychromatic418967fa.accept_13_2_3_12_1_735 93 94 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 94 220 2 46 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 94 220 (Polychromatic418967fa.accept_12_7_10_4_1_382
  91 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 94 220 2 45 47 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 94 220
  (accept_3_3 89 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 94 220 2 44 47 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 94 220
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 87 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 94 220 2 43 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 94 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 85 94 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 94 220 2 42 47 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 94 220 (accept_3_3 83 94 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 94 220 2 41 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 94 220 (Polychromatic418967fa.accept_15_6_4_10_1_2319
  81 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 94 220 2 40 47 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 94 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 79 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 94 220 2 39 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 94 220 (accept_3_3 77 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 94 220 2 38 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 94 220 (Polychromatic418967fa.accept_27_21_13_4_1_13038 75 94 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 94 220 2 37 47 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 94 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 94 220 2 36 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 94 220 (accept_3_3 71 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 94 220 2 35 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 94 220 (Polychromatic418967fa.accept_13_4_3_12_1_2066 69 94 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 94 220 2 34 47 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 94 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 94 220 2 33 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 94 220 (accept_3_3 65 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 94 220 2 32 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 94 220 (Polychromatic418967fa.accept_19_6_18_11_1_7636 63 94 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 94 220 2 31 47 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 94 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 94 220 2 30 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 94 220 (accept_3_3 59 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 94 220 2 29 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 94 220 (Polychromatic418967fa.accept_17_6_9_16_1_4410 57 94 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 94 220 2 28 47 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 94 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 94 220 2 27 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 94 220 (accept_3_3 53 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 94 220 2 26 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 94 220 (Polychromatic418967fa.accept_15_6_4_10_1_2319 51 94 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 220 2 25 47 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 220 2 24 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 94 220 (accept_3_3 47 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 94 220 2 23 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 94 220 (Polychromatic418967fa.accept_19_7_18_11_1_464 45 94 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 220 2 22 47 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 220 2 21 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 94 220 (accept_3_3 41 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 94 220 2 20 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 94 220 (Polychromatic418967fa.accept_15_9_4_10_1_2316 39 94 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 94 220 2 19 47 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 220 2 18 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 94 220 (accept_3_3 35 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 94 220 2 17 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 94 220 (Polychromatic418967fa.accept_27_6_13_4_1_13037 33 94 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 220 2 16 47 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 220 2 15 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 94 220 (accept_3_3 29 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 94 220 2 14 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 94 220 (Polychromatic418967fa.accept_17_10_9_16_1_5607 27 94 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 220 2 13 47 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 220 2 12 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 94 220 (accept_3_3 23 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 94 220 2 11 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 94 220 (Polychromatic418967fa.accept_15_6_4_10_1_2319 21 94 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 220 2 10 47 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 220 2 9 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 220 (accept_3_3 17 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  220 2 8 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 220 (Polychromatic418967fa.accept_13_2_3_12_1_735 15 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 220 2 7 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 94 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 94 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 220 2 6 47 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 220 (accept_3_3 11 94 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 220 2 5 47 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 220
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 220 2 4 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 220 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 94 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 220 2 3 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 220 (accept_3_3 5 94 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 220 2 2 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 220 (Polychromatic418967fa.accept_19_3_18_11_1_6074 3 94 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 220 2 1 47 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  94 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 220
  (allA_succ_of_accept 92 93 220 (accept_3_3 92 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 220 (accept_3_3 89 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 220 (accept_3_3 86 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 220 (Polychromatic418967fa.accept_13_6_2_12_1_2802 84 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 220 (accept_3_3 83 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 93 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 220
  (Polychromatic418967fa.accept_8_1_5_4_1_388 81 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 220 (accept_3_3 80 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 220 (accept_3_3 77 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 220 (accept_3_3 74 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 220 (Polychromatic418967fa.accept_16_8_13_12_1_3809 72 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 220 (accept_3_3 71 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 93 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 220 (accept_3_3 68 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 220 (accept_3_3 65 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 220
  (Polychromatic418967fa.accept_16_15_13_12_1_1787 63 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 93 220 (accept_3_3 62 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 93 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 93 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 93 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 220 (accept_3_3 59 93 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 220 (Polychromatic418967fa.accept_13_6_2_12_1_2802
  58 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 220 (accept_3_3 56 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 220 (accept_3_3 53 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 220 (accept_3_3 50 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 220 (accept_3_3 47 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 220
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 220 (accept_3_3 44 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 220 (accept_3_3 41 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 220
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 220 (accept_3_3 38 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 220 (accept_3_3 35 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 220 (accept_3_3 32 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 220 (accept_3_3 29 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 220 (accept_3_3 26 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 220 (accept_3_3 23 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 220
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 21 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 220 (accept_3_3 20 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 220 (accept_3_3 17 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 220 (accept_3_3 14 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 220 (accept_3_3 11 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 93 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 220
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 220 (accept_3_3 8 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 93 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 220 (accept_3_3 5 93 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 220 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 93 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 220 (Polychromatic418967fa.accept_13_3_2_12_1_2797
  3 93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 220 (accept_3_3 2 93
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  93 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 220
  (allA_of_3_1 92 92 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 220 (allA_succ_of_accept 90 91 220
  (Polychromatic418967fa.accept_16_10_11_12_1_4835 90 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 91 220 (accept_3_3 89 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 91 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 91 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 91 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 220 (accept_3_3 86 91 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 220
  (Polychromatic418967fa.accept_19_9_15_11_1_7687 85 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 91 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 220 (accept_3_3 83 91 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 82 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 81
  91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 220 (accept_3_3 80 91
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 220
  (Polychromatic418967fa.accept_8_7_3_4_1_404 79 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 91 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 91 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 220 (accept_3_3 77 91 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 91 220 (Polychromatic418967fa.accept_21_13_7_10_1_8599 76 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 91 220 (accept_3_3 74 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  91 220 (Polychromatic418967fa.accept_14_3_7_10_1_2146 73 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 220 (Polychromatic418967fa.accept_16_8_11_12_1_962 72 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 220 (accept_3_3 71 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 91 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 220 (accept_3_3 68 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 220 (Polychromatic418967fa.accept_14_11_7_10_1_4852 67 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 220 (accept_3_3 65 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 220 (Polychromatic418967fa.accept_19_7_15_11_1_3420 64 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 220 (accept_3_3 62 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 220 (accept_3_3 59 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 220 (accept_3_3 56 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 220 (Polychromatic418967fa.accept_15_9_1_10_1_4316 54 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 220 (accept_3_3 53 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 91 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 220 (accept_3_3 50 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 220 (Polychromatic418967fa.accept_16_1_11_12_1_1774 49 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 220 (accept_3_3 47 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 220 (accept_3_3 44 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 220 (accept_3_3 41 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 220 (Polychromatic418967fa.accept_16_8_11_12_1_962 40 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 220 (accept_3_3 38 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 220 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 220 (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 220 (accept_3_3 35 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 91 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 220 (accept_3_3 32 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 220 (accept_3_3 29 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 220 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 220 (accept_3_3 26 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 220 (accept_3_3 23 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 220 (accept_3_3 20 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 220 (Polychromatic418967fa.accept_21_19_7_10_1_7006 19 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 220 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 220 (accept_3_3 17 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 220 (accept_3_3 14 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 220 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 220 (accept_3_3 11 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 91 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 220 (accept_3_3 8 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  220 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 91 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 220 (accept_3_3 5 91 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 220 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 91 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 220 (accept_3_3 2 91 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 220 (Polychromatic418967fa.accept_16_1_11_12_1_1774
  1 91 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 220
  (allA_succ_of_accept 89 90 220 (accept_3_3 89 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 90
  220 2 44 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  87 90 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 87 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 90 220 2 43 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 85 90 220 5 17 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 90 220 2 42 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 220 (accept_3_3 83 90 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 90 220 2 41 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 90 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 90 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 90 220 10 8 9 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 220 2 39 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 90 220 (accept_3_3 77 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 90 220 2 38 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 90 220 5 15 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 90 220 2 37 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 90 220 (Polychromatic418967fa.accept_14_3_6_10_1_752 73 90 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 220 2 36 45 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 220 (accept_3_3 71 90 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 220 10 7 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 69
  90 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 220 2 34 45 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 220 2 33 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 90 220 5 13 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 64 90 220 2 32 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 90 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 90 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 220 2 31 45 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 220
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 61 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 90 220 10 6 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 90 220 (accept_3_3 59 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 90 220 2 29 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 90 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 90 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 220 2 28 45 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 90 220 5 11 18 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 90 220 2 27 45 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 220 (accept_3_3 53 90 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 220 2 26 45 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 220 10 5 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 220 (Polychromatic418967fa.accept_27_22_9_4_1_13036 49 90 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 220 2 24 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 220 (accept_3_3 47 90 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 220 2 23 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 220 5 9 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 90 220 2 22 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 220
  (Polychromatic418967fa.accept_16_11_10_12_1_4832 43 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 90 220 2 21 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 90 220 (accept_3_3 41 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 90 220 10 4 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 90 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 90 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 220 2 19 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 37
  90 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 220 2 18 45 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 220 5 7 18 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 90 220 2 17 45 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 220
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 220 2 16 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 90 220 (Polychromatic418967fa.accept_14_3_6_10_1_752 31 90 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 220 10 3 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 220 (accept_3_3 29 90 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 220 2 14 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 90 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 220 2 13 45 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 90 220 5 5 18 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 220 2 12 45 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 220
  (accept_3_3 23 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 220 2 11 45 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 220
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 220 10 2 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 220 (Polychromatic418967fa.accept_16_3_10_12_1_4814 19 90 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 220 2 9 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 220 (accept_3_3 17 90 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 220 2 8 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 220 5 3 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 220 2 7 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 220 (Polychromatic418967fa.accept_16_13_10_12_1_1811 13 90
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 220 2 6 45 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 220 (accept_3_3 11
  90 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 220 10 1 9 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 220 2 4 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 220 (Polychromatic418967fa.accept_19_7_14_11_1_4724 7 90 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 220 2 3 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 220 5 1 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 90 220 2 2 45 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 90 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 220 2 1 45 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 220
  (Polychromatic418967fa.accept_17_1_5_16_1_5589 1 90 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 220 (allA_of_3_1 89 89 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 220 (allA_succ_of_accept 87 88
  220 (Polychromatic418967fa.accept_9_6_7_4_1_212 87 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 88 220 2 43 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 88 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 88 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 88 220 4 21 22 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 88 220 (accept_3_3 83 88 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 88 220 2 41 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 88 220 (Polychromatic418967fa.accept_16_1_8_12_1_405
  81 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 88 220 4 20 22 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 88 220
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 79 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 88 220 2 39 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 88 220 11 7 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 88 220 4 19 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 88 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 88 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 88 220 2 37 44 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 88 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 73 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 88 220 4 18 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 88 220 (accept_3_3 71 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 88
  220 2 35 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  69 88 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 88 220 4 17 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 88 220 (Polychromatic418967fa.accept_13_2_10_12_1_757 67 88 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 88 220 22 3 4 10 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 88 220 (accept_3_3 65 88 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88 220 4 16 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 88 220
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 63 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 88 220 2 31 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 88 220 (Polychromatic418967fa.accept_13_9_10_12_1_2048 61 88 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 88 220 4 15 22 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 88 220 (accept_3_3 59 88 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88 220 2 29 44 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 88 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 88 220 4 14 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 88 220 11 5 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 88 220 2 27 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 88 220 (accept_3_3 53 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 88 220 4 13 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 88 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 88 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 88 220 2 25 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 88 220 (Polychromatic418967fa.accept_14_7_4_10_1_1351
  49 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 88 220 4 12 22 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 88 220 (accept_3_3 47
  88 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88 220 2 23 44 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 88 220
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 88 220 44 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 88 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 88 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 220 2 21 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 220 (accept_3_3 41 88 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 220 4 10 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 88 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 220 2 19 44 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 37 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 220 4 9 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 220 (accept_3_3 35 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  220 2 17 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33
  88 220 11 3 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32
  88 220 4 8 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  31 88 220 (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 88 220 2 15 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 88 220 (accept_3_3 29 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 88 220 4 7 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 88 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 88 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 220 2 13 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 220 (Polychromatic418967fa.accept_16_9_8_12_1_979
  25 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 220 4 6 22 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 220 (accept_3_3 23
  88 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 220 22 1 4 10 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 88 220 4 5 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 88 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 88 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 220 2 9 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 220 (accept_3_3 17 88 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 220 4 4 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 88 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 88 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 220 2 7 44 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 88 220 4 3 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 11 88 220 11 1 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 10 88 220 2 5 44 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 88 220 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 88 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 220 4 2 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 220 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 88 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 220 2 3 44 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 220 (accept_3_3 5 88 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 220 4 1 22 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 88
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 220 2 1 44 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 88 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87
  220 (allA_succ_of_accept 86 87 220 (accept_3_3 86 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 220 (accept_3_3 83 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 220
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 81 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 220 (accept_3_3 80 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 78 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 220 (accept_3_3 77 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 220 (Polychromatic418967fa.accept_14_6_3_10_1_3905 76 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 220
  (Polychromatic418967fa.accept_8_3_7_4_1_42 75 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 220 (accept_3_3 74 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 220 (Polychromatic418967fa.accept_16_8_7_12_1_7207 72 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 220 (accept_3_3 71 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 87 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 220
  (Polychromatic418967fa.accept_14_13_3_10_1_2159 69 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 220 (accept_3_3 68 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 220 (accept_3_3 65 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 220
  (Polychromatic418967fa.accept_14_7_3_10_1_1364 63 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 220 (accept_3_3 62 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 220 (Polychromatic418967fa.accept_13_8_9_12_1_2813 60 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 220 (accept_3_3 59 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 220 (Polychromatic418967fa.accept_15_13_12_10_1_4352 58 87
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 220 (accept_3_3 56 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 220 (accept_3_3 53 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 220
  (Polychromatic418967fa.accept_8_3_7_4_1_42 51 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 220 (accept_3_3 50 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 220 (accept_3_3 47 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 220
  (Polychromatic418967fa.accept_18_9_15_4_1_5173 45 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 220 (accept_3_3 44 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 220 (accept_3_3 41 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 220 (Polychromatic418967fa.accept_16_8_7_12_1_7207 40 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 220 (accept_3_3 38 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 220 (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 220 (accept_3_3 35 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 87 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 220
  (Polychromatic418967fa.accept_21_12_3_10_1_8575 33 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 220 (accept_3_3 32 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 220 (accept_3_3 29 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 220
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 220 (accept_3_3 26 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 220 (Polychromatic418967fa.accept_15_9_12_10_1_809 24 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 220 (accept_3_3 23 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 220 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 87
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 220 (accept_3_3 20 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 220 (accept_3_3 17 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 220
  (Polychromatic418967fa.accept_21_15_3_10_1_8533 15 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 220 (accept_3_3 14 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 220 (accept_3_3 11 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 87 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 220
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 220 (accept_3_3 8 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 87 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 220 (accept_3_3 5 87 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 220 (Polychromatic418967fa.accept_16_4_7_12_1_2734 4 87 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 220 (accept_3_3 2 87 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 87
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 220
  (allA_of_3_1 86 86 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 220 (allA_succ_of_accept 84 85 220
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 84 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 220 (accept_3_3 83 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 85 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 85 220 5 16 17 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 85 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 79 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 220 (Polychromatic418967fa.accept_19_2_9_11_1_7515 78 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 220 (accept_3_3 77 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 220 (Polychromatic418967fa.accept_13_11_7_12_1_2758 76 85 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 85 220 5 15 17 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 85 220 (accept_3_3 74 85 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 73
  85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 220 (accept_3_3 71 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 85
  220 5 14 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  85 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 85 220 (accept_3_3 68 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 85 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 220 (Polychromatic418967fa.accept_21_3_1_10_1_10008 66 85
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 85 220 5 13 17 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 85 220
  (Polychromatic418967fa.accept_18_10_13_4_1_5153 64 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 85 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 220 (accept_3_3 62 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 85 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 85 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 85 220 5 12 17 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 85 220 (accept_3_3 59 85 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 85 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 220 (accept_3_3 56 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 85
  220 5 11 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  85 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 85 220 (accept_3_3 53 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 85 220 (Polychromatic418967fa.accept_16_4_5_12_1_2749 52 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 85 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 85 220 5 10 17 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 85 220
  (Polychromatic418967fa.accept_8_1_5_4_1_388 49 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 85 220 (Polychromatic418967fa.accept_28_20_1_24_1_13035 48 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 220 (accept_3_3 47 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 85 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 85 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 85 220 5 9 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 220 (accept_3_3 44 85 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 220 (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 85 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 220
  (Polychromatic418967fa.accept_16_10_5_12_1_4925 42 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 220 (accept_3_3 41 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 85
  220 5 8 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  85 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 85 220 (accept_3_3 38 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 85 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 220 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 85
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 85 220 5 7 17 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 85 220
  (Polychromatic418967fa.accept_12_10_1_4_1_392 34 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 85 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 220 (accept_3_3 32 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 85 220 (Polychromatic418967fa.accept_13_5_7_12_1_2757 31 85 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 85 220 5 6 17 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 85 220 (accept_3_3 29 85 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 220 (Polychromatic418967fa.accept_18_10_13_4_1_5153 28 85
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 220 (accept_3_3 26 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85
  220 5 5 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  85 220 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 85 220 (accept_3_3 23 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 85 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 85 220 5 4 17 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 85 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 85 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 220 (accept_3_3 17 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 85 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 85 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 220 5 3 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 220 (accept_3_3 14 85 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 220 (Polychromatic418967fa.accept_21_13_1_10_1_5377 13 85 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 220 (accept_3_3 11 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85
  220 5 2 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  85 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 85 220 (accept_3_3 8 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 85 220 (Polychromatic418967fa.accept_16_7_5_12_1_4824 7 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 220 (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 85 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 85 220 5 1 17 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 85 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 85 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 220 (accept_3_3 2 85 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 85 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 220
  (allA_succ_of_accept 83 84 220 (accept_3_3 83 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84
  220 2 41 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  81 84 220 (Polychromatic418967fa.accept_16_1_4_12_1_376 81 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 84 220 4 20 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 84 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 84 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 220 2 39 42 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 220 (accept_3_3 77 84 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 220 4 19 21 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 220
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 75 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 220 2 37 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 84 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 220 4 18 21 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 220 (accept_3_3 71 84 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 220 2 35 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 69
  84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 220 4 17 21 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 220
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 67 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 220 2 33 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 84 220 (accept_3_3 65 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 220 4 16 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 220 (Polychromatic418967fa.accept_15_3_9_10_1_2325 63 84 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 220 2 31 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 61
  84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 220 4 15 21 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 220 (accept_3_3 59
  84 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 220 2 29 42 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 220
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 57 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 220 4 14 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 84 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 220 2 27 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 220 (accept_3_3 53 84 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 220 4 13 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 84 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 220 2 25 42 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 220
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 49 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 220 4 12 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 220 (accept_3_3 47 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84
  220 2 23 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 84 220 (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 84 220 4 11 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 84 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 84 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 220 2 21 42 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 220 (accept_3_3 41 84 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 220 4 10 21 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 220
  (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 220 2 19 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 84 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 84 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 220 4 9 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 220 (accept_3_3 35 84 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 220 2 17 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 84 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 220 4 8 21 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 220
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 31 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 220 2 15 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 84 220 (accept_3_3 29 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 220 4 7 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 84 220 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 84 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 220 2 13 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 25
  84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 220 4 6 21 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 220 (accept_3_3 23
  84 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 220 2 11 42 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 220
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 220 4 5 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 220 2 9 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 220 (accept_3_3 17 84 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 220 4 4 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 84 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 84 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 220 2 7 42 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 220
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 220 4 3 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 220 (accept_3_3 11 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84
  220 2 5 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  84 220 (Polychromatic418967fa.accept_16_9_4_12_1_4896 9 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 84 220 4 2 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 84 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 84 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 220 2 3 42 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 220 (accept_3_3 5 84 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 220 4 1 21 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 84 220 (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 84 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 220 2 1 42 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 220
  (allA_of_3_1 83 83 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 220 (allA_succ_of_accept 81 82 220
  (Polychromatic418967fa.accept_13_3_4_12_1_36 81 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 82 220 2 40 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 82 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 82 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 220 2 39 41 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 220 (accept_3_3 77 82 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 220 2 38 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 75
  82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 220 2 37 41 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 82 220 2 36 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 82 220 (accept_3_3 71 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 82 220 2 35 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 82 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 82 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 82 220 2 34 41 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 82 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 82 220 2 33 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 82 220 (accept_3_3 65 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 82 220 2 32 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 82 220 (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 82 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 82 220 2 31 41 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 82 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 61 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 82 220 2 30 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 82 220 (accept_3_3 59 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 82 220 2 29 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 82 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 82 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 220 2 28 41 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 220 2 27 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 82 220 (accept_3_3 53 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 82 220 2 26 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 82 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 82 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 82 220 2 25 41 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 82 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 82 220 2 24 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 82 220 (accept_3_3 47 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 82 220 2 23 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 82 220 (Polychromatic418967fa.accept_17_11_14_16_1_1270 45 82 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 220 2 22 41 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 82 220 2 21 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 82 220 (accept_3_3 41 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 82 220 2 20 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 82 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 82 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 220 2 19 41 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 220 2 18 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 82 220 (accept_3_3 35 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 82 220 2 17 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 82 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 82 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 220 2 16 41 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 220 2 15 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 82 220 (accept_3_3 29 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 82 220 2 14 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 82 220 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 82 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 220 2 13 41 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 220 2 12 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 82 220 (accept_3_3 23 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 82 220 2 11 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 82 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 82 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 220 2 10 41 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 220 2 9 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 220 (accept_3_3 17 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  220 2 8 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 220 2 7 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 82 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 82 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 220 2 6 41 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 220 (accept_3_3 11 82 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 220 2 5 41 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 82 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 220 2 4 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 82 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 220 2 3 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 220 (accept_3_3 5 82 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 220 2 2 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 82 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 220 2 1 41 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 82
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 220
  (allA_succ_of_accept 80 81 220 (accept_3_3 80 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 220 (accept_3_3 77 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 220
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 75 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 220 (accept_3_3 74 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 220 (Polychromatic418967fa.accept_15_12_6_10_1_1516 72 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 220 (accept_3_3 71 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 220 (Polychromatic418967fa.accept_19_13_5_11_1_7653 70 81
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 220 (accept_3_3 68 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 220 (accept_3_3 65 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 220
  (Polychromatic418967fa.accept_14_7_11_10_1_2155 63 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 220 (accept_3_3 62 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 220 (Polychromatic418967fa.accept_17_9_13_16_1_3266 60 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 220 (accept_3_3 59 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 220 (Polychromatic418967fa.accept_25_8_6_20_1_9558 58 81
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 220 (accept_3_3 56 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 220 (accept_3_3 53 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 220 (Polychromatic418967fa.accept_16_4_1_12_1_1792 52 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 220
  (Polychromatic418967fa.accept_18_15_9_4_1_5185 51 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 220 (accept_3_3 50 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 220 (accept_3_3 47 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 220 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 220
  (Polychromatic418967fa.accept_8_5_1_4_1_628 45 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 220 (accept_3_3 44 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 220 (accept_3_3 41 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 220 (Polychromatic418967fa.accept_16_8_1_12_1_984 40 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 220
  (Polychromatic418967fa.accept_25_14_6_20_1_13034 39 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 220 (accept_3_3 38 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 81 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 220 (accept_3_3 35 81 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 34
  81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 220
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 220 (accept_3_3 32 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 220 (accept_3_3 29 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 220 (Polychromatic418967fa.accept_13_2_3_12_1_735 28 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 220 (accept_3_3 26 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 220 (Polychromatic418967fa.accept_16_8_1_12_1_984 24 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 220 (accept_3_3 23 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 220
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 220 (accept_3_3 20 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 220 (accept_3_3 17 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 220 (Polychromatic418967fa.accept_15_1_6_10_1_23 16 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 220 (accept_3_3 14 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 220 (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 220 (accept_3_3 11 81 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 220 (Polychromatic418967fa.accept_19_10_5_11_1_7597 10 81
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 220
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 220 (accept_3_3 8 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 81 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 220 (accept_3_3 5 81 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 220 (Polychromatic418967fa.accept_13_4_3_12_1_2066 4 81 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 220 (Polychromatic418967fa.accept_15_3_6_10_1_1539
  3 81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 220 (accept_3_3 2 81
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  81 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 220 (allA_of_3_1 80
  80 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 220 (allA_succ_of_accept 78 79 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 78 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 220 (accept_3_3 77 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 220 (accept_3_3 74 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 79 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 220
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 72 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 220 (accept_3_3 71 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 220 (accept_3_3 68 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 79 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 220 (accept_3_3 65 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 220 (accept_3_3 62 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 79 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 220 (accept_3_3 59 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 220 (accept_3_3 56 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 79 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 220 (accept_3_3 53 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 220 (Polychromatic418967fa.accept_15_7_4_10_1_1513 52 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 220 (accept_3_3 50 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 220 (Polychromatic418967fa.accept_17_15_11_16_1_3263 49 79 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 220 (accept_3_3 47 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 220 (accept_3_3 44 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 79 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 220 (accept_3_3 41 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 220 (accept_3_3 38 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 79 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 220 (accept_3_3 35 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 220 (accept_3_3 32 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 220 (Polychromatic418967fa.accept_13_5_1_12_1_740 31 79 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 220 (accept_3_3 29 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 220 (accept_3_3 26 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 220 (Polychromatic418967fa.accept_21_4_16_10_1_10019 25 79 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 220 (accept_3_3 23 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 220 (accept_3_3 20 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 79 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 220
  (Polychromatic418967fa.accept_13_5_1_12_1_740 18 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 220 (accept_3_3 17 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 220 (Polychromatic418967fa.accept_18_16_7_4_1_3901 16 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 220 (accept_3_3 14 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 79 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 220 (accept_3_3 11 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 220 (accept_3_3 8 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 220 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 79 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 220 (accept_3_3 5 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  220 (Polychromatic418967fa.accept_16_4_15_12_1_1745 4 79 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 79 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 220 (accept_3_3 2 79 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 79 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 220
  (allA_succ_of_accept 77 78 220 (accept_3_3 77 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78
  220 2 38 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  75 78 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 78 220 2 37 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 78 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 78 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 220 2 36 39 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 220 (accept_3_3 71 78 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 220 2 35 39 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 220
  (Polychromatic418967fa.accept_12_9_6_4_1_402 69 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 220 2 34 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 78 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 78 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 220 2 33 39 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 220 (accept_3_3 65 78 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 220 2 32 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 63
  78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 220 2 31 39 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 220 2 30 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 220 (accept_3_3 59 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 78 220 2 29 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 78 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 78 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 220 2 28 39 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 55 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 220 2 27 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 220 (accept_3_3 53 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 220 2 26 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 78 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 78 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 220 2 25 39 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 220
  (Polychromatic418967fa.accept_21_7_15_10_1_1368 49 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 220 2 24 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 220 (accept_3_3 47 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 78 220 2 23 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 78 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 78 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 220 2 22 39 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 220
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 220 2 21 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 220 (accept_3_3 41 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 78 220 2 20 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 78 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 78 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 220 2 19 39 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 220 2 18 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 220 (accept_3_3 35 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 220 2 17 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 78 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 78 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 220 2 16 39 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 220
  (Polychromatic418967fa.accept_25_6_3_20_1_13033 31 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 220 2 15 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 220 (accept_3_3 29 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 220 2 14 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 78 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 78 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 220 2 13 39 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 220 2 12 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 220 (accept_3_3 23 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 220 2 11 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 78 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 78 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 220 2 10 39 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 220 2 9 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 220 (accept_3_3 17 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78
  220 2 8 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  78 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 78 220 2 7 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 78 220 (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 78 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 220 2 6 39 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 220 (accept_3_3 11 78 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 220 2 5 39 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 78 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 220 2 4 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 78 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 220 2 3 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 220 (accept_3_3 5 78 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 220 2 2 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 78 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 220 2 1 39 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 78
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 220 (allA_of_3_1 77 77
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 220 (allA_succ_of_accept 75 76 220
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 75 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 76 220 2 37 38 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 76 220 (Polychromatic418967fa.accept_14_3_6_10_1_752 73 76 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 220 4 18 19 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 220 (accept_3_3 71 76 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 220 2 35 38 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 220
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 69 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 76 220 4 17 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 76 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 76 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 76 220 2 33 38 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 76 220 (accept_3_3 65 76 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76 220 4 16 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 76 220 (Polychromatic418967fa.accept_23_17_7_13_1_13032 63 76
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 76 220 2 31 38 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 76 220
  (Polychromatic418967fa.accept_23_15_7_13_1_13029 61 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 76 220 4 15 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 76 220 (accept_3_3 59 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 76 220 2 29 38 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 76 220 (Polychromatic418967fa.accept_28_1_20_24_1_13031 57 76 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 76 220 4 14 19 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 76 220
  (Polychromatic418967fa.accept_28_27_20_24_1_13030 55 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 76 220 2 27 38 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 76 220 (accept_3_3 53 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 76 220 4 13 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 76 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 76 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 220 2 25 38 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 220
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 49 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 76 220 4 12 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 76 220 (accept_3_3 47 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 76 220 2 23 38 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 76 220 (Polychromatic418967fa.accept_14_3_6_10_1_752 45 76 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 76 220 4 11 19 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 76 220
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 43 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 76 220 2 21 38 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 76 220 (accept_3_3 41 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 76 220 4 10 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 76 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 76 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 220 2 19 38 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 37
  76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 220 4 9 19 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 220 (accept_3_3 35
  76 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76 220 2 17 38 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 76 220
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 76 220 4 8 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 76 220 (Polychromatic418967fa.accept_14_3_6_10_1_752 31 76 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 76 220 2 15 38 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 76 220 (accept_3_3 29 76 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76 220 4 7 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 76 220 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 76 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 76 220 2 13 38 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 76 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 76 220 4 6 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 76 220 (accept_3_3 23 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76
  220 2 11 38 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 76 220 (Polychromatic418967fa.accept_15_6_1_10_1_1549 21 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 76 220 4 5 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 76 220 (Polychromatic418967fa.accept_17_2_8_16_1_4403 19 76 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 220 2 9 38 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 220 (accept_3_3 17 76 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76 220 4 4 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 76 220 (Polychromatic418967fa.accept_23_15_7_13_1_13029 15 76
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 220 2 7 38 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 220
  (Polychromatic418967fa.accept_15_13_1_10_1_816 13 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 76 220 4 3 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 76 220 (accept_3_3 11 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76
  220 2 5 38 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  76 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 76 220 4 2 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 76 220 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 76 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 220 2 3 38 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 220 (accept_3_3 5 76 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 220 4 1 19 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 76 220 (Polychromatic418967fa.accept_14_3_6_10_1_752 3 76 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 220 2 1 38 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 220
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 76 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 220
  (allA_succ_of_accept 74 75 220 (accept_3_3 74 75 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  75 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 75 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 75 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 220 (accept_3_3 71 75 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 75 220 5 14 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 75 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 75 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 220 (accept_3_3 68 75 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67
  75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 75 220 5 13 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 75 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 75 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 220 (accept_3_3 62 75 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61
  75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 220 5 12 15 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 220 (accept_3_3 59
  75 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 58 75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 75 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 220 (accept_3_3 56 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 75 220 5 11 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 75 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 75 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 220 (accept_3_3 53 75 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 75 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 75 220 5 10 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 75 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 220 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 75
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 220 (accept_3_3 47 75 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 46
  75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 220 5 9 15 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 220 (accept_3_3 44
  75 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 220 (accept_3_3 41 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 75 220 5 8 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 75 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 75 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 220 (accept_3_3 38 75 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 75 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 75 220 5 7 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 75 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 220 (accept_3_3 32 75 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 220 5 6 15 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 220 (accept_3_3 29
  75 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 28 75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 220 (Polychromatic418967fa.accept_17_10_7_16_1_6841 27 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 220 (accept_3_3 26 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 75 220 5 5 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 75 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 75 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 220 (accept_3_3 23 75 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 75 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 220
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 75 220 5 4 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 75 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 75 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 220 (accept_3_3 17 75 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 16
  75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 220 5 3 15 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 220 (accept_3_3 14
  75 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 220 (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 220 (accept_3_3 11 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 75 220 5 2 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 75 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 75 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 220 (accept_3_3 8 75 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 75 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 75 220 5 1 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 75 220 (Polychromatic418967fa.accept_16_4_11_12_1_1775 4 75 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 220 (Polychromatic418967fa.accept_17_3_7_16_1_3251 3 75 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 220 (accept_3_3 2 75 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 75
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 220 (allA_of_3_1 74 74
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 220 (allA_succ_of_accept 72 73 220
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 220 (accept_3_3 71 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 220 (accept_3_3 68 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 220 (Polychromatic418967fa.accept_16_3_9_12_1_4831 67 73 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 220 (accept_3_3 65 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 220 (Polychromatic418967fa.accept_15_4_13_10_1_1508 64 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 220 (accept_3_3 62 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 73 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 220 (accept_3_3 59 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 220 (accept_3_3 56 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 220 (Polychromatic418967fa.accept_14_13_3_10_1_2159 55 73 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 220
  (Polychromatic418967fa.accept_23_8_4_13_1_13028 54 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 220 (accept_3_3 53 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 220 (accept_3_3 50 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 220 (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 73 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 220 (accept_3_3 47 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 220 (accept_3_3 44 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 73 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 220 (accept_3_3 41 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 220 (Polychromatic418967fa.accept_13_1_8_12_1_2045 40 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 220 (accept_3_3 38 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 73 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 220
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 220 (accept_3_3 35 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 220 (accept_3_3 32 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 220 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 73 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 220 (accept_3_3 29 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 220 (Polychromatic418967fa.accept_17_11_5_16_1_5600 28 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 220 (accept_3_3 26 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 73 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 220 (accept_3_3 23 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 220 (accept_3_3 20 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 220 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 73 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 220
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 220 (accept_3_3 17 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 220 (accept_3_3 14 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 73 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 220 (accept_3_3 11 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 220 (accept_3_3 8 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 220 (accept_3_3 5 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  220 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 73 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 220 (accept_3_3 2 73 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 220 (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 73 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 220 (allA_succ_of_accept 71
  72 220 (accept_3_3 71 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 220 2 35 36 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 220 4 17 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 72 220 (Polychromatic418967fa.accept_15_7_12_10_1_4335 67 72 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 220 2 33 36 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 220 (accept_3_3 65 72 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 220 4 16 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 220 (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 72
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 220 2 31 36 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 61 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 220 4 15 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 220 (accept_3_3 59 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72
  220 2 29 36 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  57 72 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 72 220 4 14 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 72 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 72 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 220 2 27 36 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 220 (accept_3_3 53 72 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 220 4 13 18 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 220
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 51 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 220 2 25 36 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 72 220 (Polychromatic418967fa.accept_13_10_7_12_1_2782 49 72 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 220 4 12 18 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 220 (accept_3_3 47 72 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 220 2 23 36 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 220
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 220 4 11 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 72 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 220 2 21 36 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 220 (accept_3_3 41 72 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 220 4 10 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 72 220 (Polychromatic418967fa.accept_15_9_12_10_1_809 39 72 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 220 2 19 36 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 220
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 37 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 220 4 9 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 220 (accept_3_3 35 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72
  220 2 17 36 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 72 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 72 220 4 8 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 72 220 (Polychromatic418967fa.accept_13_5_7_12_1_2757 31 72 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 220 2 15 36 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 220 (accept_3_3 29 72 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 220 4 7 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 220 2 13 36 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 220
  (Polychromatic418967fa.accept_16_9_8_12_1_979 25 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 220 4 6 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 220 (accept_3_3 23 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72
  220 2 11 36 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 72 220 (Polychromatic418967fa.accept_13_8_7_12_1_3637 21 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 220 4 5 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 72 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 220 2 9 36 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 220 (accept_3_3 17 72 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 220 4 4 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 220 2 7 36 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 220 4 3 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 220 (accept_3_3 11 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72
  220 2 5 36 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  72 220 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 72 220 4 2 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 72 220 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 72 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 220 2 3 36 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 220 (accept_3_3 5 72 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 220 4 1 18 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 72 220 (Polychromatic418967fa.accept_16_3_8_12_1_2736 3 72 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 220 2 1 36 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 220
  (allA_of_3_1 71 71 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 220 (allA_succ_of_accept 69 70 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 69 70 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 220 2 34 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 70 220 (Polychromatic418967fa.accept_12_7_10_4_1_382 67 70 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 220 2 33 35 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 70 220 5 13 14 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 70 220 2 32 35 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 220
  (Polychromatic418967fa.accept_19_6_13_11_1_7495 63 70 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 70 220 2 31 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 70 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 61 70 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 220 10 6 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 220 (accept_3_3 59 70 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70 220 2 29 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 70 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 70 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 220 2 28 35 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 70 220 5 11 14 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 70 220 2 27 35 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 220
  (accept_3_3 53 70 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 220 2 26 35 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 70 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 70 220 10 5 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 70 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 70 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 220 2 24 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 220 (accept_3_3 47 70 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 220 2 23 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 70 220 5 9 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 70 220 2 22 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 220 (Polychromatic418967fa.accept_12_7_10_4_1_382
  43 70 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 220 2 21 35 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 220
  (accept_3_3 41 70 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 220 10 4 7 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 70 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 70 220 2 19 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 70 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 70 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 220 2 18 35 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 70 220 5 7 14 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 70 220 2 17 35 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 70 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 70 220 2 16 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 70 220 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 70 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 220 10 3 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 220 (accept_3_3 29 70 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 220 2 14 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 220 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 70 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 220 2 13 35 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 70 220 5 5 14 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 70 220 2 12 35 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 220
  (accept_3_3 23 70 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 220 2 11 35 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 70 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 220 10 2 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 70 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 220 2 9 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 220 (accept_3_3 17 70 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 220 2 8 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 70 220 5 3 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 70 220 2 7 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 70 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 220 2 6 35 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 220 (accept_3_3 11
  70 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 220 10 1 7 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 220
  (Polychromatic418967fa.accept_21_9_7_10_1_3907 9 70 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 220 2 4 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 220 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 70 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 220 2 3 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 70 220 5 1 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 70 220 2 2 35 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 70 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 220 2 1 35 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 70 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 220
  (allA_succ_of_accept 68 69 220 (accept_3_3 68 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 220 (accept_3_3 65 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 69 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 220
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 220 (accept_3_3 62 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 220 (accept_3_3 59 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 69 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 220
  (Polychromatic418967fa.accept_8_1_5_4_1_388 57 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 220 (accept_3_3 56 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 220 (accept_3_3 53 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 69 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 220 (accept_3_3 50 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 220 (accept_3_3 47 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 69 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 220
  (Polychromatic418967fa.accept_14_3_13_10_1_761 45 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 220 (accept_3_3 44 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 220 (accept_3_3 41 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 220 (Polychromatic418967fa.accept_16_8_5_12_1_3812 40 69 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 220 (accept_3_3 38 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 220 (Polychromatic418967fa.accept_16_4_5_12_1_2749 36 69 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 220 (accept_3_3 35 69 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 69 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 220
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 220 (accept_3_3 32 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 220 (accept_3_3 29 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 69 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 220
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 220 (accept_3_3 26 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 220 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 69 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 220 (accept_3_3 23 69 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 220 (Polychromatic418967fa.accept_17_5_1_16_1_4359 22 69
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 220 (accept_3_3 20 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 220 (accept_3_3 17 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 69 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 220
  (Polychromatic418967fa.accept_13_2_4_12_1_745 15 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 220 (accept_3_3 14 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 220 (accept_3_3 11 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 69 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 220 (accept_3_3 8 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 69 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 220 (accept_3_3 5 69 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 69 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  69 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 220 (accept_3_3 2 69 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 220 (allA_of_3_1 68 68 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 220 (allA_succ_of_accept 66 67 220
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 66 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 220 (accept_3_3 65 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 220 (accept_3_3 62 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 220 (Polychromatic418967fa.accept_15_1_7_10_1_287 61 67 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 220
  (Polychromatic418967fa.accept_19_3_10_11_1_7669 60 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 220 (accept_3_3 59 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 220 (accept_3_3 56 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 67 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 220
  (Polychromatic418967fa.accept_23_8_21_13_1_13027 54 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 67 220 (accept_3_3 53 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 67 220 (Polychromatic418967fa.accept_16_4_3_12_1_4892 52 67 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 67 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 220 (accept_3_3 50 67 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 220
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 49 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 67 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 67 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 67 220 (accept_3_3 47 67 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 67 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 220 (accept_3_3 44 67
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 220 (Polychromatic418967fa.accept_7_1_4_3_1_21
  43 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 220
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 42 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 220 (accept_3_3 41 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 220 (Polychromatic418967fa.accept_13_1_2_12_1_1299 40 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 220 (accept_3_3 38 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 220 (Polychromatic418967fa.accept_19_18_10_11_1_6058 37 67 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 220 (accept_3_3 35 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 220 (accept_3_3 32 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 67 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 220
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 220 (accept_3_3 29 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 220 (Polychromatic418967fa.accept_18_10_13_4_1_5153 28 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 220 (accept_3_3 26 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 220 (Polychromatic418967fa.accept_16_9_3_12_1_1802 25 67 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 220
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 24 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 220 (accept_3_3 23 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 220 (accept_3_3 20 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 220 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 67 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 220
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 220 (accept_3_3 17 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 220 (Polychromatic418967fa.accept_13_3_2_12_1_2797 16 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 220 (accept_3_3 14 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 67 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 220
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 12 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 220 (accept_3_3 11 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 220 (accept_3_3 8 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 67 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 220 (accept_3_3 5 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  220 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 67 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 220 (accept_3_3 2 67 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 67 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 220 (allA_succ_of_accept 65 66
  220 (accept_3_3 65 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 220 2 32 33 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 220
  (Polychromatic418967fa.accept_12_3_6_4_1_400 63 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 220 2 31 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 66 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 66 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 220 2 30 33 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 220 (accept_3_3 59 66 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 220 2 29 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 57
  66 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 220 2 28 33 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 66 220 11 5 6 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 66 220 2 27 33 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 220
  (accept_3_3 53 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 220 2 26 33 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 220 2 25 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 66 220 (Polychromatic418967fa.accept_15_4_6_10_1_823 49 66 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 220 2 24 33 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 220 (accept_3_3 47 66 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 220 2 23 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 45
  66 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 220 22 2 3 10 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 220 2 21 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 220 (accept_3_3 41 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 66 220 2 20 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 66 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 66 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 220 2 19 33 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 220 2 18 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 220 (accept_3_3 35 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 66 220 2 17 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 66 220 11 3 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 66 220 2 16 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 66 220 (Polychromatic418967fa.accept_13_5_1_12_1_740 31 66 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 220 2 15 33 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 220 (accept_3_3 29 66 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 220 2 14 33 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 220
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 220 2 13 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 66 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 66 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 220 2 12 33 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 220 (accept_3_3 23 66 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 220 22 1 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 66 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 220 2 10 33 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 220 2 9 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 220 (accept_3_3 17 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  220 2 8 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 220 2 7 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 66 220 (Polychromatic418967fa.accept_21_13_3_10_1_2592 13 66 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 220 2 6 33 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 66 220 11 1 6 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 66 220 2 5 33 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 220
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 66 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 220 2 4 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 66 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 220 2 3 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 220 (accept_3_3 5 66 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 66 220 2 2 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 66 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 66 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 220 2 1 33 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 66
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 220 (allA_of_3_1 65 65 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 220 (allA_succ_of_accept 63 64 220
  (Polychromatic418967fa.accept_17_12_13_16_1_3226 63 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 64 220 2 31 32 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 64 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 64 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 220 4 15 16 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 220 (accept_3_3 59 64 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 220 2 29 32 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 57 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 220 4 14 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 220 (Polychromatic418967fa.accept_21_13_1_10_1_5377 55 64 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 220 2 27 32 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 220 (accept_3_3 53 64 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 220 4 13 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 64 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 220 2 25 32 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 220
  (Polychromatic418967fa.accept_18_13_10_4_1_5150 49 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 220 4 12 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 220 (accept_3_3 47 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  220 2 23 32 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 64 220 (Polychromatic418967fa.accept_21_3_1_10_1_10008 45 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 220 4 11 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 220 2 21 32 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 220 (accept_3_3 41 64 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 220 4 10 16 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 64 220 2 19 32 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 64 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 64 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 220 4 9 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 220 (accept_3_3 35 64 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64 220 2 17 32 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 64 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 64 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 220 4 8 16 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 220
  (Polychromatic418967fa.accept_18_13_10_4_1_5150 31 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 220 2 15 32 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 64 220 (accept_3_3 29 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 64 220 4 7 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 64 220 (Polychromatic418967fa.accept_19_8_7_11_1_11722 27 64 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 220 2 13 32 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 25
  64 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 220 4 6 16 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 220 (accept_3_3 23
  64 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 220 2 11 32 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 64 220 4 5 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 64 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 64 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 220 2 9 32 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 220 (accept_3_3 17 64 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 220 4 4 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 64 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 64 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 220 2 7 32 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 220
  (Polychromatic418967fa.accept_15_13_4_10_1_821 13 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 220 4 3 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 220 (accept_3_3 11 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64
  220 2 5 32 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  64 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 64 220 4 2 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 64 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 220 2 3 32 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 220 (accept_3_3 5 64 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 220 4 1 16 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 64 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 64 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 220 2 1 32 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 220
  (Polychromatic418967fa.accept_23_1_18_13_1_13026 1 64 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 220
  (allA_succ_of_accept 62 63 220 (accept_3_3 62 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 220 (Polychromatic418967fa.accept_14_4_7_10_1_3888 60 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 220 (accept_3_3 59 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 220 (Polychromatic418967fa.accept_15_13_3_10_1_2296 58 63
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 220
  (Polychromatic418967fa.accept_23_11_17_13_1_13025 57 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 63 220 (accept_3_3 56 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 63 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 220 (accept_3_3 53 63 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 220 (Polychromatic418967fa.accept_15_7_3_10_1_817
  52 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 220
  (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 220 (accept_3_3 50 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 220 (Polychromatic418967fa.accept_18_12_9_4_1_2740 48 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 220 (accept_3_3 47 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 220 (Polychromatic418967fa.accept_13_7_11_12_1_2051 46 63
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 220
  (Polychromatic418967fa.accept_14_3_7_10_1_2146 45 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 220 (accept_3_3 44 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 63 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 220 (accept_3_3 41 63 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 220 (Polychromatic418967fa.accept_13_1_11_12_1_1322 40 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 220
  (Polychromatic418967fa.accept_14_11_7_10_1_4852 39 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 220 (accept_3_3 38 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 220 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 220 (accept_3_3 35 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 220 (Polychromatic418967fa.accept_16_2_15_12_1_1744 34 63
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 220
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 220 (accept_3_3 32 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 63 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 220 (accept_3_3 29 63 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 220 (Polychromatic418967fa.accept_15_13_3_10_1_2296 28 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 220
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 220 (accept_3_3 26 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 220 (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 220 (accept_3_3 23 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 220 (Polychromatic418967fa.accept_15_7_3_10_1_817 22 63 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 220
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 21 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 220 (accept_3_3 20 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 63 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 220 (accept_3_3 17 63 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 220 (Polychromatic418967fa.accept_19_16_6_11_1_6052 16 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 220
  (Polychromatic418967fa.accept_18_15_9_4_1_5185 15 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 220 (accept_3_3 14 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 220 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 220 (accept_3_3 11 63 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 220 (Polychromatic418967fa.accept_13_10_11_12_1_1320 10 63
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 220
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 220 (accept_3_3 8 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 63 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 220 (accept_3_3 5 63 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 220 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 63 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 220 (accept_3_3 2 63 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 63
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 220 (allA_of_3_1 62 62 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 220 (allA_succ_of_accept 60 61 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 220 (accept_3_3 59 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 220 (accept_3_3 56 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 61 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 220
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 54 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 220 (accept_3_3 53 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 220 (Polychromatic418967fa.accept_15_7_1_10_1_305 52 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 220 (accept_3_3 50 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 61 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 220 (accept_3_3 47 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 220 (accept_3_3 44 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 61 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 220 (accept_3_3 41 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 220 (Polychromatic418967fa.accept_14_12_5_10_1_2130 40 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 220 (accept_3_3 38 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 61 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 220 (accept_3_3 35 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 220 (accept_3_3 32 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 220 (Polychromatic418967fa.accept_16_15_13_12_1_1787 31 61 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 220 (accept_3_3 29 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 220 (accept_3_3 26 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 61 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 220 (accept_3_3 23 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 220 (accept_3_3 20 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 220
  (Polychromatic418967fa.accept_19_18_4_11_1_11751 18 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 61 220 (accept_3_3 17 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 61 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 61 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 61 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 220 (accept_3_3 14 61 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 220 (Polychromatic418967fa.accept_15_13_1_10_1_816
  13 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 220 (accept_3_3 11 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 220 (accept_3_3 8 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 220 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 61 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 220 (accept_3_3 5 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  220 (Polychromatic418967fa.accept_16_4_13_12_1_1740 4 61 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 220 (accept_3_3 2 61 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 220 (allA_succ_of_accept 59 60 220
  (accept_3_3 59 60 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 220 2 29 30 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 60 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 60 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 60 220 4 14 15 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 60 220 5 11 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 60 220 2 27 30 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 60 220 (accept_3_3 53 60 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 60 220 4 13 15 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 60 220 (Polychromatic418967fa.accept_18_15_6_4_1_5147 51 60 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 220 10 5 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 220 (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 60
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 220 4 12 15 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 220 (accept_3_3 47
  60 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 220 2 23 30 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 220 5 9 12 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 220 4 11 15 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 60 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 220 2 21 30 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 60 220 (accept_3_3 41 60 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 220 20 2 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 60 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 220 2 19 30 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 37
  60 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 220 4 9 15 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 220 5 7 12 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 60 220 2 17 30 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 220
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 60 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 220 4 8 15 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 220 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 60 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 220 10 3 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 220 (accept_3_3 29 60 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 220 4 7 15 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 220 2 13 30 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 220 5 5 12 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 220 4 6 15 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 220 (accept_3_3 23 60 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 220 2 11 30 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 21
  60 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 220 20 1 3 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 60 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 220 2 9 30 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 220 (accept_3_3 17 60 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60
  220 4 4 15 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60
  220 5 3 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60
  220 2 7 30 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13
  60 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 60 220 4 3 15 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 60 220 (accept_3_3 11 60 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 220 10 1 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 60 220 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 60 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 220 4 2 15 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 220 2 3 30 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 60 220 5 1 12 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 60 220 4 1 15 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 60 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 220 2 1 30 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 220 (allA_of_3_1 59 59 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 220
  (allA_succ_of_accept 57 58 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 58 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 58 220 2 28 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 58 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 55
  58 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 220 2 27 29 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 220 (accept_3_3 53
  58 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 220 2 26 29 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 220
  (Polychromatic418967fa.accept_16_3_10_12_1_4814 51 58 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 58 220 2 25 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 58 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 58 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 58 220 2 24 29 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 58 220 (accept_3_3 47 58 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 220 2 23 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 220
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 45 58 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 220 2 22 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 58 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 220 2 21 29 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 220 (accept_3_3 41 58 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 220 2 20 29 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 220
  (Polychromatic418967fa.accept_25_14_8_20_1_13024 39 58 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 58 220 2 19 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 58 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 58 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 220 2 18 29 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 220 (accept_3_3 35 58 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 220 2 17 29 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 58 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 58 220 2 16 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 58 220 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 58 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 220 2 15 29 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 220 (accept_3_3 29 58 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 220 2 14 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 27
  58 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 220 2 13 29 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 58 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 220 2 12 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 58 220 (accept_3_3 23 58 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 58 220 2 11 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 58 220 (Polychromatic418967fa.accept_16_5_10_12_1_4904 21 58 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 220 2 10 29 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 58 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 220 2 9 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 220 (accept_3_3 17 58 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  220 2 8 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 58 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 220 2 7 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 58 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 58 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 220 2 6 29 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 220 (accept_3_3 11 58 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 220 2 5 29 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 220
  (Polychromatic418967fa.accept_19_9_1_11_1_7643 9 58 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 220 2 4 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 220 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 58 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 220 2 3 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 220 (accept_3_3 5 58 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 220 2 2 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 220 (Polychromatic418967fa.accept_15_3_13_10_1_2332 3 58 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 220 2 1 29 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 58
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 220 (allA_succ_of_accept 56 57 220
  (accept_3_3 56 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 55 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 57 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 220 (accept_3_3 53 57 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 51
  57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 220 (accept_3_3 50 57
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 220
  (Polychromatic418967fa.accept_21_6_15_10_1_2579 48 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 220 (accept_3_3 47 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 220 (accept_3_3 44 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 57 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 220 (accept_3_3 41 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 220 (accept_3_3 38 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 220
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 220 (accept_3_3 35 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 220 (accept_3_3 32 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 57 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 220 (accept_3_3 29 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 220 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 220 (accept_3_3 26 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 220 (accept_3_3 23 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 220 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 220 (accept_3_3 20 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 57 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 220 (accept_3_3 17 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 220 (accept_3_3 14 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 220 (accept_3_3 11 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 220 (accept_3_3 8 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 57 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 220 (accept_3_3 5 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  220 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 57 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 220 (Polychromatic418967fa.accept_16_3_9_12_1_4831 3 57 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 220 (accept_3_3 2 57 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 220 (allA_of_3_1 56 56 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 220
  (allA_succ_of_accept 54 55 220 (Polychromatic418967fa.accept_13_2_3_12_1_735 54 55 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 220 (accept_3_3 53 55 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 55 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 220 5 10 11 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 220
  (Polychromatic418967fa.accept_17_15_4_16_1_6890 49 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 220 (accept_3_3 47 55 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 55 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 220 5 9 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 55 220 11 4 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 55 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 43
  55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 220 (accept_3_3 41 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  220 5 8 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 220 (accept_3_3 38 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 55 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 220 (Polychromatic418967fa.accept_16_4_7_12_1_2734 36 55
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 220 5 7 11 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 34 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 55 220 11 3 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 55 220 (accept_3_3 32 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 220 (Polychromatic418967fa.accept_14_3_13_10_1_761 31 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 55 220 5 6 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 55 220 (accept_3_3 29 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 55 220 (Polychromatic418967fa.accept_13_2_3_12_1_735 28 55 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 220 (accept_3_3 26 55 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55 220 5 5 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 55 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 24
  55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 220 (accept_3_3 23 55
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 55 220 11 2 5 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 55 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 55 220 5 4 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 55 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 55 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 55 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 220 (accept_3_3 17 55 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 16
  55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 220 5 3 11 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 220 (accept_3_3 14
  55 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 220
  (Polychromatic418967fa.accept_19_13_17_11_1_4716 13 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 55 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 55 220 11 1 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 55 220 5 2 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 55 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 55
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 220 (accept_3_3 8 55 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7
  55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 55 220 5 1 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 55 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 55 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 220 (accept_3_3 2 55 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 220
  (Polychromatic418967fa.accept_21_1_13_10_1_11627 1 55 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 55 220))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 220 (allA_succ_of_accept 53 54
  220 (accept_3_3 53 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 220 2 26 27 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 54 220 2 25 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 54 220 (Polychromatic418967fa.accept_13_10_2_12_1_1332 49 54 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 220 2 24 27 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 220 (accept_3_3 47 54 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 220 2 23 27 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 220
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 220 2 22 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 54 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 54 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 220 2 21 27 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 220 (accept_3_3 41 54 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 220 2 20 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 39
  54 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 220 2 19 27 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 220 2 18 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 220 (accept_3_3 35 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 220 2 17 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 54 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 54 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 220 2 16 27 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 220
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 220 2 15 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 220 (accept_3_3 29 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 220 2 14 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 54 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 54 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 220 2 13 27 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 220
  (Polychromatic418967fa.accept_19_6_16_11_1_9041 25 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 220 2 12 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 220 (accept_3_3 23 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 220 2 11 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 54 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 54 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 220 2 10 27 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 220
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 220 2 9 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 220 (accept_3_3 17 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54
  220 2 8 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  54 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 54 220 2 7 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 54 220 (Polychromatic418967fa.accept_17_13_3_16_1_5599 13 54 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 220 2 6 27 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 220 (accept_3_3 11 54 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 220 2 5 27 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 54 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 54 220 2 4 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 220 (Polychromatic418967fa.accept_17_7_3_16_1_2208 7 54 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 220 2 3 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 220 (accept_3_3 5 54 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 54 220 2 2 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 54 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 54 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 220 2 1 27 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 54
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 220 (allA_of_3_1 53 53 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 220 (allA_succ_of_accept 51 52 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 51
  52 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 220 2 25 26 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 220
  (Polychromatic418967fa.accept_15_4_7_10_1_807 49 52 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 52 220 4 12 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 52 220 (accept_3_3 47 52 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52
  220 2 23 26 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 52 220 (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 52 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 52 220 4 11 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 52 220 (Polychromatic418967fa.accept_16_11_4_12_1_1760 43 52 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 220 2 21 26 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 220 (accept_3_3 41 52 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 220 4 10 13 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 52 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 52 220 2 19 26 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 52 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 52 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 220 4 9 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 220 (accept_3_3 35 52 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 220 2 17 26 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 52 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 220 4 8 13 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 220
  (Polychromatic418967fa.accept_15_1_7_10_1_287 31 52 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 220 2 15 26 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 52 220 (accept_3_3 29 52 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 52 220 4 7 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 52 220 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 52 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 220 2 13 26 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 220 (Polychromatic418967fa.accept_16_9_4_12_1_4896
  25 52 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 220 4 6 13 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 220 (accept_3_3 23
  52 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 220 2 11 26 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 52 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 52 220 4 5 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 52 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 52 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 220 2 9 26 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 220 (accept_3_3 17 52 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 220 4 4 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 52 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 52 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 220 2 7 26 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 220
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 52 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 220 4 3 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 220 (accept_3_3 11 52 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  220 2 5 26 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 220 (Polychromatic418967fa.accept_16_9_4_12_1_4896 9 52 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 52 220 4 2 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 52 220 (Polychromatic418967fa.accept_16_7_4_12_1_1806 7 52 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 220 2 3 26 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 220 (accept_3_3 5 52 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 220 4 1 13 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 52 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 52 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 220 2 1 26 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 52 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 220)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 220 (allA_succ_of_accept 50 51 220
  (accept_3_3 50 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 49 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 220 (accept_3_3 47 51 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 220 (Polychromatic418967fa.accept_18_9_15_4_1_5173
  45 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 220 (accept_3_3 44
  51 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 51 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 220 (accept_3_3 41 51 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 39
  51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 220 (accept_3_3 38 51
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  37 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 220 (accept_3_3 35 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 220 (accept_3_3 32 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 220 (accept_3_3 29 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 220 (accept_3_3 26 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 51 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 220
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 24 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 220 (accept_3_3 23 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 220 (accept_3_3 20 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 220 (accept_3_3 17 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 220 (accept_3_3 14 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 51 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 220 (accept_3_3 11 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 220 (Polychromatic418967fa.accept_16_9_3_12_1_1802 9 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 220 (accept_3_3 8 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 220 (accept_3_3 5 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  220 (Polychromatic418967fa.accept_15_4_6_10_1_823 4 51 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 220 (accept_3_3 2 51 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 51 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  220))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 220 (allA_of_3_1 50 50 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 220 (allA_succ_of_accept 48 49 220 (Polychromatic418967fa.accept_13_9_10_12_1_2048
  48 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 220 (accept_3_3 47
  49 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 220
  (Polychromatic418967fa.accept_12_10_1_4_1_392 46 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 49 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 220 (accept_3_3 44 49 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 49 220 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 49 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 220
  (Polychromatic418967fa.accept_25_17_24_20_1_13023 42 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 49 220 (accept_3_3 41 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 49 220 (Polychromatic418967fa.accept_16_8_1_12_1_984 40 49 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 49 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 220 (accept_3_3 38 49 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 37
  49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 220
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 36 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 220 (accept_3_3 35 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 220 (accept_3_3 32 49 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 220 (Polychromatic418967fa.accept_14_3_7_10_1_2146 31 49 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 220
  (Polychromatic418967fa.accept_21_9_7_10_1_3907 30 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 220 (accept_3_3 29 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 220 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 49 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 220 (accept_3_3 26 49 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 220 (Polychromatic418967fa.accept_14_11_7_10_1_4852 25 49 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 220
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 49 220 (accept_3_3 23 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 49 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 49 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 220 (accept_3_3 20 49 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 220
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 19 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 220 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 49 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 220 (accept_3_3 17 49 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 220 (Polychromatic418967fa.accept_21_16_7_10_1_8601 16 49 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 220 (accept_3_3 14 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 220 (Polychromatic418967fa.accept_23_12_3_13_1_13022 12 49 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 220 (accept_3_3 11 49 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 49 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 220 (accept_3_3 8 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  220 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 220 (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 49 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 220 (accept_3_3 5 49 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 220 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 49 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 220 (accept_3_3 2 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  220 (Polychromatic418967fa.accept_17_1_15_16_1_2202 1 49 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 49 220))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 220 (allA_succ_of_accept
  47 48 220 (accept_3_3 47 48 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 220 2 23 24 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 220
  (Polychromatic418967fa.accept_14_3_6_10_1_752 45 48 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 220 4 11 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 48 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 220 2 21 24 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 220 (accept_3_3 41 48 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 220 4 10 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 220 2 19 24 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 48 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 220 4 9 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 220 (accept_3_3 35 48 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48
  220 2 17 24 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 48 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 48 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 48 220 4 8 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 48 220 (Polychromatic418967fa.accept_14_3_6_10_1_752 31 48 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 220 2 15 24 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 220 (accept_3_3 29 48 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 220 4 7 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 220 (Polychromatic418967fa.accept_18_9_12_4_1_1659 27 48 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 220 2 13 24 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 220 4 6 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 220 (accept_3_3 23 48 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48
  220 2 11 24 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 48 220 (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 48 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 48 220 4 5 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 48 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 220 2 9 24 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 220 (accept_3_3 17 48 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 220 4 4 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 48 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 220 2 7 24 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 220
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 48 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 220 4 3 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 220 (accept_3_3 11 48 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48
  220 2 5 24 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  48 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 48 220 4 2 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 48 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 220 2 3 24 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 220 (accept_3_3 5 48 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 220 4 1 12 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 48 220 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 48 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 220 2 1 24 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 48 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 220)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 220 (allA_of_3_1 47 47 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 46 220 (allA_succ_of_accept 45 46 220
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 46 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 220 2 22 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 46 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 46 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 220 2 21 23 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 220 (accept_3_3 41 46 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 220 2 20 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 39
  46 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 220 2 19 23 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 46 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 220 2 18 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 46 220 (accept_3_3 35 46 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 46 220 2 17 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 46 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 46 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 220 2 16 23 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 46 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 220 2 15 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 46 220 (accept_3_3 29 46 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 46 220 2 14 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 46 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 220 2 13 23 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 46 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 46 220 2 12 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 46 220 (accept_3_3 23 46 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 46 220 2 11 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 46 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 46 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 220 2 10 23 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 46 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 220 2 9 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 220 (accept_3_3 17 46 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  220 2 8 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 46 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 220 2 7 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 46 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 46 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 220 2 6 23 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 220 (accept_3_3 11 46 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 220 2 5 23 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 220
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 46 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 220 2 4 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 46 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 220 2 3 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 220 (accept_3_3 5 46 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 220 2 2 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 46 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 220 2 1 23 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 46
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  220)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 220 (allA_succ_of_accept 44 45 220 (accept_3_3 44 45
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 220 (accept_3_3 41 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45
  220 5 8 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  45 220 (Polychromatic418967fa.accept_17_5_11_16_1_3257 39 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 45 220 (accept_3_3 38 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 220 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 45
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 45 220 5 7 9 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 220
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 34 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 45 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 45 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 220 (accept_3_3 32 45 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 45 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 45 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 220 5 6 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 220 (accept_3_3 29 45 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 220 (Polychromatic418967fa.accept_13_2_6_12_1_1334 28 45 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 220
  (Polychromatic418967fa.accept_14_13_3_10_1_2159 27 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 220 (accept_3_3 26 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45
  220 5 5 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  45 220 (Polychromatic418967fa.accept_16_8_13_12_1_3809 24 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 220 (accept_3_3 23 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 220 (Polychromatic418967fa.accept_17_5_11_16_1_3257 22 45 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 220 (Polychromatic418967fa.accept_14_7_3_10_1_1364 21 45
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 45 220 5 4 9 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 45 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 45 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 220 (accept_3_3 17 45 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 45 220 (Polychromatic418967fa.accept_21_16_3_10_1_6978 16 45 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 220 5 3 9 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 220 (accept_3_3 14 45 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 220
  (Polychromatic418967fa.accept_17_12_11_16_1_6903 12 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 220 (accept_3_3 11 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 45 220 5 2 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 45 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 45 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 220 (accept_3_3 8 45 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 45 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 45 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 6
  45 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 45 220 5 1 9 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 220
  (Polychromatic418967fa.accept_16_4_13_12_1_1740 4 45 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 220 (Polychromatic418967fa.accept_23_3_22_13_1_13021 3 45 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 220 (accept_3_3 2 45 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 220))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  220 (allA_of_3_1 44 44 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 220 (allA_succ_of_accept 42 43 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 220 (accept_3_3 41 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 220 (accept_3_3 38 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 43 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 220
  (Polychromatic418967fa.accept_16_4_11_12_1_1775 36 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 220 (accept_3_3 35 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 220 (accept_3_3 32 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 43 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 220 (accept_3_3 29 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 220 (accept_3_3 26 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 43 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 220 (accept_3_3 23 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 220 (accept_3_3 20 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 220 (accept_3_3 17 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 220 (accept_3_3 14 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 220 (Polychromatic418967fa.accept_17_13_9_16_1_3254 13 43 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 220 (accept_3_3 11 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 220 (accept_3_3 8 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 43 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 220 (accept_3_3 5 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  220 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 43 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 220 (accept_3_3 2 43 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 220))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 220
  (allA_succ_of_accept 41 42 220 (accept_3_3 41 42 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42
  220 2 20 21 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 42 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 42 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 42 220 2 19 21 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 42 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 42 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 220 2 18 21 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 220 (accept_3_3 35 42 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 220 2 17 21 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 220
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 42 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 220 2 16 21 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 220 (Polychromatic418967fa.accept_17_14_8_16_1_6863 31 42 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 220 2 15 21 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 220 (accept_3_3 29 42 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 220 2 14 21 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 220
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 42 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 42 220 2 13 21 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 42 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 42 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 220 2 12 21 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 220 (accept_3_3 23 42 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 220 2 11 21 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 21
  42 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 220 2 10 21 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 42 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 220 2 9 21 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 220 (accept_3_3 17 42 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42
  220 2 8 21 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  42 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 42 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 42 220 2 7 21 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 42 220 (Polychromatic418967fa.accept_15_13_12_10_1_4352 13 42 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 220 2 6 21 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 220 (accept_3_3 11 42 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 220 2 5 21 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 220
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 42 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 220 2 4 21 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 42 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 220 2 3 21 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 220 (accept_3_3 5 42 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 220 2 2 21 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 42 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 220 2 1 21 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 42
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  220)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 220 (allA_of_3_1 41 41 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 220 (allA_succ_of_accept 39 40 220 (Polychromatic418967fa.accept_16_7_8_12_1_4902 39 40 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 220 2 19 20 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 40 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 220 4 9 10 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 40 220 5 7 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 40 220 2 17 20 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 40 220 (Polychromatic418967fa.accept_14_5_12_10_1_2985 33 40 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 220 4 8 10 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 220
  (Polychromatic418967fa.accept_13_5_1_12_1_740 31 40 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 220 10 3 4 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 220 (accept_3_3 29 40 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  220 4 7 10 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 220 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 40 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 220 2 13 20 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 40 220 5 5 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 40 220 4 6 10 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 40 220 (accept_3_3 23 40 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 40 220 2 11 20 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 40 220 (Polychromatic418967fa.accept_13_8_1_12_1_762 21 40 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 220 20 1 2 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 220 (Polychromatic418967fa.accept_14_5_12_10_1_2985
  19 40 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 220 2 9 20 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 220 (accept_3_3 17
  40 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 220 4 4 10 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 40 220 5 3 8 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 40 220 2 7 20 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 220
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 13 40 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 40 220 4 3 10 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 40 220 (accept_3_3 11 40 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  220 10 1 4 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  40 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 40 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 40 220 4 2 10 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 40 220 (Polychromatic418967fa.accept_16_7_8_12_1_4902 7 40 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 220 2 3 20 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 40 220 5 1 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 40 220 4 1 10 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40 220 (Polychromatic418967fa.accept_16_3_8_12_1_2736 3
  40 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 220 2 1 20 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 40 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 220)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 220 (allA_succ_of_accept 38 39 220 (accept_3_3
  38 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 220 (accept_3_3 35 39 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 39 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 33
  39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 220 (accept_3_3 32 39
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 220 (accept_3_3 29 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 220 (accept_3_3 26 39 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 39 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 220 (accept_3_3 23 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 220 (Polychromatic418967fa.accept_14_7_11_10_1_2155 21 39 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 220 (accept_3_3 20 39 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 220 (accept_3_3 17 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 220 (accept_3_3 14 39 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 39 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 220
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 220 (accept_3_3 11 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 220 (Polychromatic418967fa.accept_19_9_1_11_1_7643 9 39 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 220 (accept_3_3 8 39 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 220 (accept_3_3 5 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  220 (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 39 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 39 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 220 (accept_3_3 2 39 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 39 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 220))))))))))))))))))))))))))))))))))))))) (allB_succ
  38 220 (allA_of_3_1 38 38 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 220 (allA_succ_of_accept 36 37
  220 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 220 (accept_3_3 35 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 220 (accept_3_3 32 37 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 220 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 37 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 220 (accept_3_3 29 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 220 (Polychromatic418967fa.accept_21_7_16_10_1_1349 28 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 37 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 220 (accept_3_3 26 37 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 37 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 220 (accept_3_3 23 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 220 (accept_3_3 20 37 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 37 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 220
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 18 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 220 (accept_3_3 17 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 37 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 220 (accept_3_3 14 37 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 37 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 220 (accept_3_3 11 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 220 (accept_3_3 8 37 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 220 (accept_3_3 5 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  220 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 37 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 37 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 37 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 220 (accept_3_3 2 37 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 220))))))))))))))))))))))))))))))))))))) (allB_succ
  36 220 (allA_succ_of_accept 35 36 220 (accept_3_3 35 36 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  34 36 220 2 17 18 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 220 4 8 9 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 220 (Polychromatic418967fa.accept_15_1_6_10_1_23 31 36 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 220 2 15 18 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 220 (accept_3_3 29
  36 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 220 4 7 9 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 220
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 36 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 220 2 13 18 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 36 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 220 4 6 9 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 220 (accept_3_3 23 36 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 220 2 11 18 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 220 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 36
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 220 4 5 9 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 220 2 9 18 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 220 (accept_3_3 17 36 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36
  220 4 4 9 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  36 220 (Polychromatic418967fa.accept_13_2_10_12_1_757 15 36 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 220 2 7 18 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 36 220 (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 36 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 220 4 3 9 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 220 (accept_3_3 11 36 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 220 2 5 18 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 220 4 2 9 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 220
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 36 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 220 2 3 18 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 220 (accept_3_3 5 36 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 220
  4 1 9 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 220
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 36 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 220 2 1 18 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 220 (Polychromatic418967fa.accept_15_1_6_10_1_23 1 36 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 220)))))))))))))))))))))))))))))))))))) (allB_succ 35 220 (allA_of_3_1 35
  35 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 220 (allA_succ_of_accept 33 34 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 34 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 220 2 16 17 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 34 220 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 34 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 220 2 15 17 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 220 (accept_3_3 29 34 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 220 2 14 17 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 220 (Polychromatic418967fa.accept_13_1_8_12_1_2045
  27 34 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 220 2 13 17 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 34 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 220 2 12 17 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 34 220 (accept_3_3 23 34 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 34 220 2 11 17 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 34 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 34 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 34 220 2 10 17 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 34 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 34 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 34 220 2 9 17 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 34 220 (accept_3_3 17 34 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34
  220 2 8 17 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  34 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 34 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 34 220 2 7 17 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 34 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 34 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 220 2 6 17 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 220 (accept_3_3 11 34 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 220 2 5 17 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 34 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 220 2 4 17 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 220 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 34 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 220 2 3 17 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 220 (accept_3_3 5 34 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 220 2 2 17 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 34 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 220 2 1 17 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 34
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 220))))))))))))))))))))))))))))))))))
  (allB_succ 33 220 (allA_succ_of_accept 32 33 220 (accept_3_3 32 33 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 33 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 33 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 220 (accept_3_3 29 33 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 28
  33 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 220
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 27 33 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 220 (accept_3_3 26 33 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 220 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 33 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 220 (accept_3_3 23 33 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 33 220 11 2 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 33 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 220 (accept_3_3 20 33 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  33 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 33 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 220 (accept_3_3 17 33 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 33 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 33 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 220 (accept_3_3 14 33 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 33 220 11 1 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 33 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 33 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 220 (accept_3_3 8 33 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 33
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 33 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 220 (accept_3_3 5 33 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  220 (Polychromatic418967fa.accept_13_4_7_12_1_2823 4 33 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 33 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 220 (accept_3_3 2 33 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 220))))))))))))))))))))))))))))))))) (allB_succ 32
  220 (allA_of_3_1 32 32 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 220 (allA_succ_of_accept 30 31 220
  (Polychromatic418967fa.accept_13_4_5_12_1_751 30 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 220 (accept_3_3 29 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 220 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 220 (accept_3_3 26 31 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 220 (Polychromatic418967fa.accept_17_8_14_16_1_6849 25 31 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 220
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 24 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 220 (accept_3_3 23 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 31 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 220 (accept_3_3 20 31 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 31 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 220
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 18 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 220 (accept_3_3 17 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 220 (Polychromatic418967fa.accept_23_16_8_13_1_13020 16 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 220 (accept_3_3 14 31 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 220 (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 31 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 220
  (Polychromatic418967fa.accept_24_12_7_4_1_13019 12 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 220 (accept_3_3 11 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 31 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 220 (accept_3_3 8 31 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 220 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 31 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 220
  (Polychromatic418967fa.accept_13_6_5_12_1_307 6 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 220 (accept_3_3 5 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  220 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 31 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 220 (accept_3_3 2 31 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 220 (Polychromatic418967fa.accept_13_1_5_12_1_306 1 31 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 220))))))))))))))))))))))))))))))) (allB_succ 30 220
  (allA_succ_of_accept 29 30 220 (accept_3_3 29 30 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  220 2 14 15 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 30 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 30 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 220 2 13 15 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 30 220 5 5 6 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 220 2 12 15 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 220 (accept_3_3 23 30 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 30 220 2 11 15 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 30 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 30 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 220 10 2 3 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 30 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 220 2 9 15 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 220 (accept_3_3 17 30 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30
  220 2 8 15 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30
  220 5 3 6 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30
  220 2 7 15 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13
  30 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 30 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 30 220 2 6 15 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 30 220 (accept_3_3 11 30 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 220 10 1 3 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 30 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 220 2 4 15 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 30 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 220 2 3 15 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 220 5 1 6 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 30 220 2 2 15 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 220
  (Polychromatic418967fa.accept_12_3_6_4_1_400 3 30 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 30 220 2 1 15 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 30 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 220)))))))))))))))))))))))))))))) (allB_succ 29 220 (allA_of_3_1 29 29
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 220 (allA_succ_of_accept 27 28 220
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 28 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 220 2 13 14 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 28 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 28 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 220 4 6 7 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 220 (accept_3_3 23 28 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 220 2 11 14 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 28 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 220 4 5 7 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 220
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 28 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 220 2 9 14 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 220 (accept_3_3 17 28 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  220 4 4 7 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 28 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 220 2 7 14 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 28 220 (Polychromatic418967fa.accept_18_13_10_4_1_5150 13 28 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 220 4 3 7 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 220 (accept_3_3 11 28 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 220 2 5 14 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 220 (Polychromatic418967fa.accept_21_9_7_10_1_3907 9
  28 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 220 4 2 7 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 28 220 2 3 14 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 220 (accept_3_3 5 28 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 220
  4 1 7 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 28 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 220 2 1 14 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 220 (Polychromatic418967fa.accept_13_1_2_12_1_1299 1 28 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 220)))))))))))))))))))))))))))) (allB_succ 27 220 (allA_succ_of_accept 26
  27 220 (accept_3_3 26 27 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 25 27 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 27 220 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 27 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 220 (accept_3_3 23 27 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 27 220 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 27 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 220
  (Polychromatic418967fa.accept_13_8_1_12_1_762 21 27 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 220 (accept_3_3 20 27 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 27 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 220 (accept_3_3 17 27 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 27 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 220
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 27 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 220 (accept_3_3 14 27 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 27 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 220 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 27 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 220 (accept_3_3 11 27 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 220 (Polychromatic418967fa.accept_16_10_11_12_1_4835 10 27
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 27 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 220 (accept_3_3 8 27 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 27 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 220 (accept_3_3 5 27 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 27 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 220 (Polychromatic418967fa.accept_14_3_13_10_1_761
  3 27 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 220 (accept_3_3 2 27
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  27 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 220)))))))))))))))))))))))))))
  (allB_succ 26 220 (allA_of_3_1 26 26 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 220
  (allA_succ_of_accept 24 25 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 25 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 220 (accept_3_3 23 25 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 25 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  25 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 220 5 4 5 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 25 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 220 (Polychromatic418967fa.accept_16_2_9_12_1_46 18 25 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 220 (accept_3_3 17 25 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 220 (Polychromatic418967fa.accept_18_16_7_4_1_3901 16 25 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 25 220 5 3 5 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 25 220 (accept_3_3 14 25 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 25 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 220 (accept_3_3 11 25 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25
  220 5 2 5 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25
  220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 220 (accept_3_3 8 25 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  220 (Polychromatic418967fa.accept_14_7_11_10_1_2155 7 25 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 25 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 25 220 5 1 5 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 25 220 (Polychromatic418967fa.accept_16_4_9_12_1_4829 4
  25 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 25 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 220 (accept_3_3 2 25 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 220))))))))))))))))))))))))) (allB_succ 24 220 (allA_succ_of_accept 23 24 220 (accept_3_3 23 24 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 220 2 11 12 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 220 4 5 6 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 24 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 220 2 9 12 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 220 (accept_3_3 17 24 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 220 4 4 6 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 24 220 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 24 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 220 2 7 12 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 220
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 13 24 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 220 4 3 6 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 220 (accept_3_3 11 24 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  220 2 5 12 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 220 (Polychromatic418967fa.accept_16_9_8_12_1_979 9 24 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 24 220 4 2 6 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 24 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 220 2 3 12 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 220 (accept_3_3 5 24 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 220 4 1 6 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 24 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 24 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 220 2 1 12 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 24 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 220)))))))))))))))))))))))) (allB_succ 23 220 (allA_of_3_1 23 23 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 220 (allA_succ_of_accept 21 22 220 (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 22 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 220 2 10 11 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 22 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 22 220 2 9 11 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 22 220 (accept_3_3 17 22 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22
  220 2 8 11 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  22 220 (Polychromatic418967fa.accept_21_15_1_10_1_8592 15 22 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 22 220 2 7 11 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 22 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 22 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 220 2 6 11 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 22 220 11 1 2 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 22 220 2 5 11 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 22 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 220 2 4 11 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 220 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 22 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 220 2 3 11 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 220 (accept_3_3 5 22 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 220 2 2 11 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 220 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 22 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 220 2 1 11 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  22 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 220)))))))))))))))))))))) (allB_succ
  21 220 (allA_succ_of_accept 20 21 220 (accept_3_3 20 21 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 21 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 21 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 220 (accept_3_3 17 21 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 16
  21 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 220 (accept_3_3 14 21 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 220 (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 21 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 220 (accept_3_3 11 21 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 21 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 220
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 220 (accept_3_3 8 21 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 21 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 21 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 220 (accept_3_3 5 21 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 220 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 21 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 220 (Polychromatic418967fa.accept_14_3_7_10_1_2146
  3 21 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 220 (accept_3_3 2 21
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  21 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 220))))))))))))))))))))) (allB_succ
  20 220 (allA_of_3_1 20 20 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 220 (allA_succ_of_accept 18 19
  220 (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 19 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 220 (accept_3_3 17 19 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 19 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 220 (accept_3_3 14 19 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 220 (Polychromatic418967fa.accept_15_13_4_10_1_821
  13 19 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 220 (accept_3_3 11 19 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 19 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 19 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 220 (accept_3_3 8 19 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 19 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 19 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 220 (accept_3_3 5 19 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  220 (Polychromatic418967fa.accept_16_4_3_12_1_4892 4 19 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 19 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 220 (accept_3_3 2 19 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 19 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 220))))))))))))))))))) (allB_succ 18 220
  (allA_succ_of_accept 17 18 220 (accept_3_3 17 18 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18
  220 2 8 9 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  18 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 18 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 18 220 2 7 9 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 18 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 220 2 6 9 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 220 (accept_3_3 11 18 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 220 2 5 9 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 18 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 18 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 220 2 4 9 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 220
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 18 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 220 2 3 9 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 220 (accept_3_3 5 18 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 220
  2 2 9 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18
  220 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 18 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 220 2 1 9 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 18 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 220)))))))))))))))))) (allB_succ 17 220 (allA_of_3_1 17 17 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 220 (allA_succ_of_accept 15 16 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 16 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 220 2 7 8 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 16 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 220 4 3 4 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 220 (accept_3_3 11 16 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 220 2 5 8 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 220 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 16 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 220 4 2 4 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 220 (Polychromatic418967fa.accept_15_7_1_10_1_305 7
  16 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 220 2 3 8 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 220 (accept_3_3 5 16
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 220 4 1 4 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 16 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 220 2 1 8 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 16 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 220)))))))))))))))) (allB_succ 15 220 (allA_succ_of_accept 14 15 220
  (accept_3_3 14 15 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 15 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 220 (accept_3_3 11 15 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 15 220 5 2 3 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 15 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 15 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 220 (accept_3_3 8 15 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 15 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 15 220 5 1 3 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 15 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 15 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 15 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 220 (accept_3_3 2 15 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 15
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 220))))))))))))))) (allB_succ 14 220
  (allA_of_3_1 14 14 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 220 (allA_succ_of_accept 12 13 220
  (Polychromatic418967fa.accept_15_12_13_10_1_812 12 13 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 220 (accept_3_3 11 13 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 13 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 220 (accept_3_3 8 13 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 220 (Polychromatic418967fa.accept_18_7_13_4_1_1670 7 13 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 220
  (Polychromatic418967fa.accept_19_6_13_11_1_7495 6 13 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 220 (accept_3_3 5 13 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  220 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 13 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 13 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 220 (accept_3_3 2 13 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 13 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 220))))))))))))) (allB_succ 12 220 (allA_succ_of_accept 11 12
  220 (accept_3_3 11 12 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 220 2 5 6 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 220 4 2 3 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 220 2 3 6 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 220 (accept_3_3 5 12 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 220 4 1 3 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 220 (Polychromatic418967fa.accept_19_3_12_11_1_7619 3 12 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 220 2 1 6 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 220)))))))))))) (allB_succ 11 220
  (allA_of_3_1 11 11 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 220 (allA_succ_of_accept 9 10 220
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 10 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 220 2 4 5 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 10 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 220 2 3 5 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 10 220 5 1 2 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 10 220 2 2 5 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 10 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 220 2 1 5 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 10 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 220)))))))))) (allB_succ 9 220 (allA_succ_of_accept 8 9 220 (accept_3_3 8 9 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 9 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 9 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 220 (accept_3_3 5 9 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 220
  (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 9 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 220 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 9 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 220 (accept_3_3 2 9 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 220))))))))) (allB_succ 8 220 (allA_of_3_1 8 8 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 220 (allA_succ_of_accept 6 7 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 7 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 220 (accept_3_3 5 7 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 220
  (Polychromatic418967fa.accept_13_4_7_12_1_2823 4 7 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 220 (accept_3_3 2 7 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 220))))))) (allB_succ 6 220 (allA_succ_of_accept 5 6 220
  (accept_3_3 5 6 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 220 2 2 3 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 6 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 220 2 1 3 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 6 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 220)))))) (allB_succ 5 220 (allA_of_3_1 5 5 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 220 (allA_succ_of_accept 3 4 220 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 4
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 220 2 1 2 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 4 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 220)))) (allB_succ 3 220 (allA_succ_of_accept 2 3 220 (accept_3_3 2 3 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 220))) (allB_succ 2 220 (allA_of_3_1 2 2 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


