-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch280_Segment001
-- name    : Polychromatic418967fa_Branch280_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:55:05.866368+00:00
-- url     : https://prove2.me/theorems/5e5a77ca-efd3-4d7d-8748-007f65a694f7
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch280_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_280_segment_001 : allB 186 280 :=
  allB_succ' 96 185 280 (Eq.refl Bool.true) (allA_of_3_1 96 185 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  97 184 280 (Eq.refl Bool.true) (allA_succ_of_gcd 96 184 280 8 12 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 184 280 (accept_3_3 95 184 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 94 184 280 2 47 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 184 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 93 184 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 184 280 4 23 46 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 184 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 91 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 184 280 2 45 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 184 280 (accept_3_3 89 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 184 280 8 11 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 184 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 87 184 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 184 280 2 43 92 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 184 280
  (Polychromatic418967fa.accept_18_13_4_10_1_1076 85 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 184 280 4 21 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 184 280 (accept_3_3 83 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 184 280 2 41 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 184 280 (Polychromatic418967fa.accept_15_6_4_10_1_2319 81 184 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 184 280 8 10 23 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 184 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 79 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 184 280 2 39 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 184 280 (accept_3_3 77 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 184 280 4 19 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 184 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 75 184 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 184 280 2 37 92 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 184 280
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 73 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 184 280 8 9 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 184 280 (accept_3_3 71 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  184 280 2 35 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 184 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 184 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 184 280 4 17 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 184 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513
  67 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 184 280 2 33 92 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 184 280
  (accept_3_3 65 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 184 280 8 8 23 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 184 280
  (Polychromatic418967fa.accept_22_19_8_16_1_3106 63 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 184 280 2 31 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 184 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 184 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 184 280 4 15 46 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 184 280 (accept_3_3 59 184 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 184 280 2 29 92 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 184 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 184 280 8 7 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 184 280 (Polychromatic418967fa.accept_21_13_16_7_1_3712 55 184 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 184 280 2 27 92 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 184 280 (accept_3_3 53 184 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 184 280 4 13 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 184 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 51
  184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 184 280 2 25 92 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 184 280
  (Polychromatic418967fa.accept_18_13_4_10_1_1076 49 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 184 280 8 6 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 184 280 (accept_3_3 47 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 184 280 2 23 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 184 280 (Polychromatic418967fa.accept_17_11_14_8_1_2729 45 184 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 184 280 4 11 46 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 184 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 184 280 2 21 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 184 280 (accept_3_3 41 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 184 280 8 5 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 184 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 184 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 184 280 2 19 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 184 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513
  37 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 184 280 4 9 46 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 184 280
  (accept_3_3 35 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 184 280 2 17 92 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 184 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 184 280 8 4 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 184 280 (Polychromatic418967fa.accept_13_5_2_7_1_2414 31 184 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 184 280 2 15 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 184 280 (accept_3_3 29 184 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 184 280 4 7 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 184 280 (Polychromatic418967fa.accept_19_8_13_14_1_2373 27 184
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 280 2 13 92 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 184 280 8 3 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 184 280 (accept_3_3 23 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  184 280 2 11 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 184 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 184 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 184 280 4 5 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 184 280
  (Polychromatic418967fa.accept_22_19_8_16_1_3106 19 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 184 280 2 9 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 184 280 (accept_3_3 17 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 184 280 8 2 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 184 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 184 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 280 2 7 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219
  13 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 184 280 4 3 46 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 184 280
  (accept_3_3 11 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 184 280 2 5 92 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 184 280
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 184 280 8 1 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 184 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 184 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 184 280 2 3 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 184 280 (accept_3_3 5 184 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184 280 4 1 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 184 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 184 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 184 280 2 1 92 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 184 280
  (Polychromatic418967fa.accept_19_1_13_14_1_3509 1 184 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 184 280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 98 183 280 (Eq.refl Bool.true) (allA_succ_of_accept 97 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  97 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 183 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 96 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 183 280 (accept_3_3 95 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 183 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 94 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 183 280 (Polychromatic418967fa.accept_19_17_12_14_1_3655 93 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 183 280 (accept_3_3 92 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 183 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 183 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 90 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 183 280 (accept_3_3 89 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 183 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 88 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 183 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 183 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 183 280 (accept_3_3 86 183 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 183 280
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 84 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 183 280 (accept_3_3 83 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 183 280 (Polychromatic418967fa.accept_15_7_3_10_1_817 82 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 183 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 81 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 183 280 (accept_3_3 80 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 183 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 183 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 183 280 (accept_3_3 77 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 183 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 183 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 75 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 183 280 (accept_3_3 74 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 183 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 183 280
  (Polychromatic418967fa.accept_17_4_13_8_1_3874 72 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 183 280 (accept_3_3 71 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 183 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 183 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 183 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 183 280 (accept_3_3 68 183 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 183 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 183 280 (accept_3_3 65 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 183 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 64 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 183 280 (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 183 280 (accept_3_3 62 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 183 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 183 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 183 280 (accept_3_3 59 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 183 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 183 280 (Polychromatic418967fa.accept_16_9_7_8_1_1588 57 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 183 280 (accept_3_3 56 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 183 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 183 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 183 280 (accept_3_3 53 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 183 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 183 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 183 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 183 280 (accept_3_3 50 183 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 183 280
  (Polychromatic418967fa.accept_19_10_12_14_1_3613 48 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 183 280 (accept_3_3 47 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 183 280 (Polychromatic418967fa.accept_29_17_9_19_1_17211 46 183 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 183 280 (Polychromatic418967fa.accept_13_6_1_7_1_1690
  45 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 280 (accept_3_3 44
  183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 183 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 183 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 183 280 (accept_3_3 41 183 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 183 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 183 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 183 280
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 183 280 (accept_3_3 38 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 183 280 (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 280 (accept_3_3 35 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 183 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 183 280 (accept_3_3 32 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 183 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 280 (accept_3_3 29 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 280 (Polychromatic418967fa.accept_15_13_3_10_1_2296 28 183
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 280
  (Polychromatic418967fa.accept_22_5_7_16_1_1788 27 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 183 280 (accept_3_3 26 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 183 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 183 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 280 (accept_3_3 23 183 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 280
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 183 280 (accept_3_3 20 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 183 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 280 (accept_3_3 17 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 183 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 183 280 (accept_3_3 14 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 183 280 (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 280 (accept_3_3 11 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 280 (Polychromatic418967fa.accept_19_10_12_14_1_3613 10
  183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 280
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 183 280 (accept_3_3 8 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 183 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 183 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 280 (accept_3_3 5 183 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 183 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 280
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 3 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 183 280 (accept_3_3 2 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  183 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 183 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 183
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  182 280 (Eq.refl Bool.true) (allA_of_3_1 99 182 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 181 280
  (Eq.refl Bool.true) (allA_succ_of_accept 99 181 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 181 280 (accept_3_3 98 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 181 280 (Polychromatic418967fa.accept_13_6_12_7_1_5131 97 181
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 181 280
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 96 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 181 280 (accept_3_3 95 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 181 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 94 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 181 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 181 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 181 280 (accept_3_3 92 181 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 181 280 (Polychromatic418967fa.accept_16_11_5_8_1_2427 91 181 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 181 280
  (Polychromatic418967fa.accept_21_6_13_7_1_8394 90 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 181 280 (accept_3_3 89 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 181 280 (Polychromatic418967fa.accept_13_10_12_7_1_1079 88 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 181 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 181 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 181 280 (accept_3_3 86 181 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 181 280 (Polychromatic418967fa.accept_18_13_1_10_1_4331 85 181 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 181 280
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 84 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 181 280 (accept_3_3 83 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 181 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 181 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 181 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 181 280 (accept_3_3 80 181 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 181 280 (Polychromatic418967fa.accept_21_16_13_7_1_8385 79 181 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 181 280
  (Polychromatic418967fa.accept_21_15_13_7_1_5175 78 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 181 280 (accept_3_3 77 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 181 280 (Polychromatic418967fa.accept_13_11_12_7_1_2443 76 181 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 181 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 75
  181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 181 280 (accept_3_3 74
  181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 181 280
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 73 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 181 280 (Polychromatic418967fa.accept_19_15_10_14_1_3652 72 181 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 181 280 (accept_3_3 71 181 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 181 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 181 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 181 280 (accept_3_3 68 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 181 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 67 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 181 280 (Polychromatic418967fa.accept_15_6_1_10_1_1549 66 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 181 280 (accept_3_3 65 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 181 280 (Polychromatic418967fa.accept_19_7_10_14_1_3599 64 181
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 181 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 181 280 (accept_3_3 62 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 181 280 (Polychromatic418967fa.accept_16_13_5_8_1_5814 61 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 181 280 (Polychromatic418967fa.accept_13_8_12_7_1_2442 60 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 181 280 (accept_3_3 59 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 181 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 181
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 181 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 181 280 (accept_3_3 56 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 181 280 (Polychromatic418967fa.accept_22_11_5_16_1_6222 55 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 181 280 (Polychromatic418967fa.accept_15_9_1_10_1_4316 54 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 181 280 (accept_3_3 53 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 181 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 52 181
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 181 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 181 280 (accept_3_3 50 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 181 280 (Polychromatic418967fa.accept_13_10_12_7_1_1079 49 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 181 280 (Polychromatic418967fa.accept_17_14_11_8_1_3854 48 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 280 (accept_3_3 47 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 181 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 181
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 181 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 181 280 (accept_3_3 44 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 181 280 (Polychromatic418967fa.accept_13_4_12_7_1_2439 43 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 181 280 (Polychromatic418967fa.accept_19_4_10_14_1_7833 42 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 280 (accept_3_3 41 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 280 (Polychromatic418967fa.accept_21_19_13_7_1_3706 40 181
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 181 280 (accept_3_3 38 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 181 280 (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 181 280 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 280 (accept_3_3 35 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 181
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 280 (accept_3_3 32 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 280 (Polychromatic418967fa.accept_13_5_12_7_1_1080 31 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 280 (Polychromatic418967fa.accept_13_4_12_7_1_2439 30 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 280 (accept_3_3 29 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 181
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 280 (accept_3_3 26 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 280 (Polychromatic418967fa.accept_19_6_10_14_1_3542 25 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 280 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 280 (accept_3_3 23 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 181
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 280 (accept_3_3 20 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 280 (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 280 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 280 (accept_3_3 17 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 280 (Polychromatic418967fa.accept_18_16_1_10_1_2029 16 181
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 280 (accept_3_3 14 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 280 (Polychromatic418967fa.accept_16_12_5_8_1_2492 12 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 280 (accept_3_3 11 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 181
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 280 (accept_3_3 8 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 280 (Polychromatic418967fa.accept_13_6_12_7_1_5131 6 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 280 (accept_3_3 5 181 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 280 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 181
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 280 (accept_3_3 2 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 280 (Polychromatic418967fa.accept_17_1_11_8_1_2725 1 181 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 180 280 (Eq.refl Bool.true) (allA_succ_of_gcd 100 180 280 20 5 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 180 280 (Polychromatic418967fa.accept_16_3_4_8_1_3450
  99 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 180 280 2 49 90 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 180 280
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 97 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 180 280 4 24 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 95 180 280 5 19 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 94 180 280 2 47 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 180 280 (Polychromatic418967fa.accept_16_13_4_8_1_4557 93 180
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 180 280 4 23 45 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 180 280
  (Polychromatic418967fa.accept_16_11_4_8_1_3435 91 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 180 280 10 9 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 180 280 (accept_3_3 89 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 180 280 4 22 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 180 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 87 180 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 180 280 2 43 90 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 180 280 5 17 36 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 180 280 4 21 45 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 180 280
  (accept_3_3 83 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 180 280 2 41 90 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 180 280
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 81 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 180 280 20 4 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 180 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 79 180 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 180 280 2 39 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 180 280 (accept_3_3 77 180 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 76 180 280 4 19 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 180 280 5 15 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 180 280 2 37 90 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 180 280
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 73 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 180 280 4 18 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 180 280 (accept_3_3 71 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 180 280 10 7 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 180 280 (Polychromatic418967fa.accept_13_4_11_7_1_558 69 180 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 180 280 4 17 45 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 180 280
  (Polychromatic418967fa.accept_16_3_4_8_1_3450 67 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 180 280 2 33 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 180 280 5 13 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 180 280 4 16 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 180 280 (Polychromatic418967fa.accept_16_15_4_8_1_1562 63 180
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 180 280 2 31 90 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 180 280
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 61 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 180 280 20 3 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 180 280 (accept_3_3 59 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58
  180 280 2 29 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 180 280 (Polychromatic418967fa.accept_13_5_11_7_1_559 57 180 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 180 280 4 14 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 180 280 5 11 36 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 180 280 2 27 90 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 180 280 (accept_3_3 53 180 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 180 280 4 13 45 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 180 280
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 51 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 180 280 10 5 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 180 280 (Polychromatic418967fa.accept_16_1_4_8_1_3434 49 180 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 180 280 4 12 45 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 180 280 (accept_3_3 47 180 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 280 2 23 90 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 180 280 5 9 36 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 180 280 4 11 45 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 280
  (Polychromatic418967fa.accept_11_10_4_5_1_359 43 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 280 2 21 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 280 (accept_3_3 41 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 180 280 20 2 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 180 280 (Polychromatic418967fa.accept_16_7_4_8_1_2487 39 180 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 180 280 2 19 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 280 (Polychromatic418967fa.accept_16_5_4_8_1_1560
  37 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 180 280 4 9 45 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 180 280 5 7 36 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 180 280 2 17 90
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 180 280
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 33 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 180 280 4 8 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 180 280 (Polychromatic418967fa.accept_13_5_11_7_1_559 31 180 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 180 280 10 3 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 180 280 (accept_3_3 29 180 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 280 4 7 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 180 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 180
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 180 280 2 13 90 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 180 280 5 5 36 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 180 280 4 6 45 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 180 280 (accept_3_3 23
  180 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 280 2 11 90 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 180 280
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 180 280 20 1 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 180 280 (Polychromatic418967fa.accept_16_3_4_8_1_3450 19 180 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 180 280 2 9 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 180 280 (accept_3_3 17 180 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 280 4 4 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 280 5 3 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 280 2 7 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 280 (Polychromatic418967fa.accept_16_13_4_8_1_4557
  13 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 280 4 3 45 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 280
  (accept_3_3 11 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 280 10 1 18 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 280
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 180 280 4 2 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 180 280 (Polychromatic418967fa.accept_16_7_4_8_1_2487 7 180 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 280 2 3 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 180 280 5 1 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 180 280 4 1 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 180 280 (Polychromatic418967fa.accept_13_3_11_7_1_2488
  3 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 280 2 1 90 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 280
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 180 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 180 280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 102 179 280 (Eq.refl Bool.true) (allA_of_3_1 102 179 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 103 178 280 (Eq.refl Bool.true) (allA_succ_of_gcd 102 178 280 2 51 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 178 280 (accept_3_3 101 178 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 178 280 2 50 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 178 280 (Polychromatic418967fa.accept_13_8_9_7_1_530
  99 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 178 280 2 49 89 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 178 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 97 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 178 280 2 48 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 178 280 (accept_3_3 95 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 178 280 2 47 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 178 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 93 178 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 178 280 2 46 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 178 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 91 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 178 280 2 45 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 178 280 (accept_3_3 89 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 178 280 2 44 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 178 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 87 178 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 178 280 2 43 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 178 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 85 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 178 280 2 42 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 178 280 (accept_3_3 83 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 178 280 2 41 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 178 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 81 178 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 178 280 2 40 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 178 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 79 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 178 280 2 39 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 178 280 (accept_3_3 77 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 178 280 2 38 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 178 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 178 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 178 280 2 37 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 178 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 178 280 2 36 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 178 280 (accept_3_3 71 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 178 280 2 35 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 178 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 178 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 178 280 2 34 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 178 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 67 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 178 280 2 33 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 178 280 (accept_3_3 65 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 178 280 2 32 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 178 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 178 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 178 280 2 31 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 178 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 178 280 2 30 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 178 280 (accept_3_3 59 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 178 280 2 29 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 178 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 178 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 178 280 2 28 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 178 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 178 280 2 27 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 178 280 (accept_3_3 53 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 178 280 2 26 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 178 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 178 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 178 280 2 25 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 178 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 178 280 2 24 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 178 280 (accept_3_3 47 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 178 280 2 23 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 178 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 178 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 178 280 2 22 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 178 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 178 280 2 21 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 178 280 (accept_3_3 41 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 178 280 2 20 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 178 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 178 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 178 280 2 19 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 178 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 178 280 2 18 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 178 280 (accept_3_3 35 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 178 280 2 17 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 178 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 178 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 280 2 16 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 280 2 15 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 280 (accept_3_3 29 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 280 2 14 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 27 178 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 280 2 13 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 178 280 2 12 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 178 280 (accept_3_3 23 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 280 2 11 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 178 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 280 2 10 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 280
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 280 2 9 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 280 (accept_3_3 17 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 280 2 8 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 178 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 280 2 7 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 280 2 6 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 280 (accept_3_3 11 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 280 2 5 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 280 (Polychromatic418967fa.accept_21_9_10_7_1_383 9 178 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 280 2 4 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 280 2 3 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 280 (accept_3_3 5 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  280 2 2 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 178 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 280 2 1 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 178 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 177 280 (Eq.refl Bool.true) (allA_succ_of_accept 103 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 177 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 102 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 177 280 (accept_3_3 101 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 177 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 100 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 177 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 99 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 177 280 (accept_3_3 98 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 177 280
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 96 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 177 280 (accept_3_3 95 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 177 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 94 177 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 177 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 177 280 (accept_3_3 92 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91
  177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 177 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 90 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 177 280 (accept_3_3 89 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 177 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 88 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 177 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 87 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 177 280 (accept_3_3 86 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 177 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 177 280 (accept_3_3 83 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 177 280 (Polychromatic418967fa.accept_15_7_12_10_1_4335 82 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 177 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135 81 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 177 280 (accept_3_3 80 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 177 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 78 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 177 280 (accept_3_3 77 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 177 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 177 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 177 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 177 280 (accept_3_3 74 177 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 177 280
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 177 280 (accept_3_3 71 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 177 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 177 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 69 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 177 280 (accept_3_3 68 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 177 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 177 280 (accept_3_3 65 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 177 280 (Polychromatic418967fa.accept_13_12_8_7_1_2526 64 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 177 280 (Polychromatic418967fa.accept_16_15_1_8_1_1585 63 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 177 280 (accept_3_3 62 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 177 280
  (Polychromatic418967fa.accept_16_12_1_8_1_5767 60 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 177 280 (accept_3_3 59 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 177 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 177 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 177 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 177 280 (accept_3_3 56 177 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 177 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 177 280 (accept_3_3 53 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 177 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 177 280 (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 177 280 (accept_3_3 50 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 177 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 177 280 (accept_3_3 47 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 177 280 (Polychromatic418967fa.accept_19_8_6_14_1_5009 46 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 177 280 (Polychromatic418967fa.accept_18_9_15_10_1_395 45 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 177 280 (accept_3_3 44 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 177 280 (accept_3_3 41 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 177 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 177 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 177 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 280 (accept_3_3 38 177 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 280
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 177 280 (accept_3_3 35 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 177 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 177 280 (Polychromatic418967fa.accept_17_16_7_8_1_7638 33 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 280 (accept_3_3 32 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 177 280 (accept_3_3 29 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 177 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 177 280 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 280 (accept_3_3 26 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 280
  (Polychromatic418967fa.accept_15_9_12_10_1_809 24 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 177 280 (accept_3_3 23 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 177 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 177 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 177 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 280 (accept_3_3 20 177 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 177 280 (accept_3_3 17 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 177 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 177 280 (Polychromatic418967fa.accept_13_2_8_7_1_2424 15 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 280 (accept_3_3 14 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 177 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 280 (accept_3_3 11 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 177 280 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 177 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 280 (accept_3_3 8 177 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 280
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 280 (accept_3_3 5 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  177 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 177 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 177 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 280 (accept_3_3 2 177 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 177 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 176 280 (Eq.refl Bool.true) (allA_of_3_1 105 176 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 106 175 280 (Eq.refl Bool.true) (allA_succ_of_gcd 105 175 280 35 3 5 8 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 175 280 (accept_3_3 104 175 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 175 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 103
  175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 175 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 102 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 175 280 (accept_3_3 101 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  100 175 280 5 20 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 99 175 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 175 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 175 280 7 14 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 175 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 97
  175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 175 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 96 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 95 175 280 5 19 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 94 175 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 94 175 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 175 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 175 280 (accept_3_3 92 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91
  175 280 7 13 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  90 175 280 5 18 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 175 280 (accept_3_3 89 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 175 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 175 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 175 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 175 280 (accept_3_3 86 175 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 85 175 280 5 17 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 175 280 7 12 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 175 280 (accept_3_3 83 175 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 175 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 82 175 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 175 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 175 280 5 16 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 175 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 175 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 175 280 (Polychromatic418967fa.accept_9_6_4_1_1_390
  78 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 175 280 7 11 25 40
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 175 280
  (Polychromatic418967fa.accept_16_12_15_8_1_4586 76 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 175 280 5 15 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 175 280 (accept_3_3 74 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 175 280 (Polychromatic418967fa.accept_16_9_15_8_1_3425 73 175 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 175 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 72 175
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 175 280 (accept_3_3 71 175
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 175 280 35 2 5 8 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 175 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 175 280 (accept_3_3 68 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 175 280 (Polychromatic418967fa.accept_19_10_4_14_1_4981 67 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 175 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 175 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 175 280 5 13 35 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 175 280
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 64 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 175 280 7 9 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 175 280 (accept_3_3 62 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 175 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 175 280 5 12 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 175 280 (accept_3_3 59 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 175 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 175 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 175 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 175 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 175 280 7 8 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 175 280 5 11 35 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 175 280
  (Polychromatic418967fa.accept_17_3_5_8_1_1687 54 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 175 280 (accept_3_3 53 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 175 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 175 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 175 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 175 280 5 10 35 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 175 280 7 7 25 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 175 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 175 280 (accept_3_3 47 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 175 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 175 280 5 9 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 175 280 (accept_3_3 44 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 175 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 175 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 175 280 7 6 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 175 280 (accept_3_3 41 175 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 175 280 5 8 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 175 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 175 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 280 (accept_3_3 38 175 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 280
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 175 280 (Polychromatic418967fa.accept_16_4_15_8_1_2413 36 175 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 175 280 35 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 175 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 175 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 280 (accept_3_3 32 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 280 (Polychromatic418967fa.accept_29_2_1_19_1_17210 31 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 175 280 5 6 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 175 280 (accept_3_3 29 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 175 280 7 4 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 175 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 175 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 280 (accept_3_3 26 175 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 175 280 5 5 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 175 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 175 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 280 (accept_3_3 23 175 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 175
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 175 280 7 3 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 175 280 5 4 35 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 175 280
  (Polychromatic418967fa.accept_18_1_13_10_1_2024 19 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 280 (Polychromatic418967fa.accept_19_18_4_14_1_14577 18 175 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 280 (accept_3_3 17 175 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 175 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 175 280 5 3 35 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 175 280 7 2 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 175 280
  (Polychromatic418967fa.accept_17_13_5_8_1_896 13 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 175 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 175 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 280 (accept_3_3 11 175 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 175 280 5 2 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 175 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 175 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 280 (accept_3_3 8 175 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 175 280 7 1 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 175 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 175 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 175 280 5 1 35 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 175 280
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 175 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 175 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 175 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 280 (accept_3_3 2 175 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 175 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 175 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 174 280 (Eq.refl Bool.true) (allA_succ_of_gcd 106 174 280 2 53 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 174 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 105 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 174 280 2 52 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 174 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 103 174 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 174 280 2 51 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 174 280 (accept_3_3 101 174 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 174 280 2 50 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 174 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 99 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 174 280 2 49 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 174 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 97 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 174 280 2 48 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 174 280 (accept_3_3 95 174 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 174 280 2 47 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 174 280 (Polychromatic418967fa.accept_12_9_6_4_1_402
  93 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 174 280 2 46 87 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 174 280
  (Polychromatic418967fa.accept_15_1_9_10_1_2327 91 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 174 280 2 45 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 174 280 (accept_3_3 89 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 174 280 2 44 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 174 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 174 280 2 43 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 174 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 85 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 174 280 2 42 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 174 280 (accept_3_3 83 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 174 280 2 41 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 174 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 174 280 2 40 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 174 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 79 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 174 280 2 39 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 174 280 (accept_3_3 77 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 174 280 2 38 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 174 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 75 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 174 280 2 37 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 174 280
  (Polychromatic418967fa.accept_11_7_9_5_1_338 73 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 174 280 2 36 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 174 280 (accept_3_3 71 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 174 280 2 35 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 174 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 174 280 2 34 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 174 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 67 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 174 280 2 33 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 280 (accept_3_3 65 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 174 280 2 32 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 174 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 174 280 2 31 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 174 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 280 2 30 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 280 (accept_3_3 59 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 174 280 2 29 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 174 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 174 280 2 28 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 174 280
  (Polychromatic418967fa.accept_19_17_3_14_1_14557 55 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 174 280 2 27 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 174 280 (accept_3_3 53 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 174 280 2 26 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 174 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 174 280 2 25 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 280 2 24 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 280 (accept_3_3 47 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 174 280 2 23 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 174 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 174 280 2 22 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 280 2 21 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 280 (accept_3_3 41 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 174 280 2 20 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 174 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 174 280 2 19 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 280
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 37 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 280 2 18 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 280 (accept_3_3 35 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 174 280 2 17 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 174 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 174 280 2 16 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 280 2 15 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 280 (accept_3_3 29 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 174 280 2 14 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 174 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 174 280 2 13 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 280 2 12 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 280 (accept_3_3 23 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 174 280 2 11 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 174 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 174 280 2 10 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 280
  (Polychromatic418967fa.accept_15_4_9_10_1_5384 19 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 280 2 9 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 280 (accept_3_3 17 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 174 280 2 8 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 174 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 174 280 2 7 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 280 2 6 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 280 (accept_3_3 11 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 280 2 5 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 174 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 174 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 174 280 2 4 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 280 2 3 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 280 (accept_3_3 5 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174
  280 2 2 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  174 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 174 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 174 280 2 1 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 174 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 1 174 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 173 280 (Eq.refl Bool.true) (allA_of_3_1 108 173 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 109 172 280 (Eq.refl Bool.true) (allA_succ_of_gcd 108 172 280 4 27 43 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 172 280 (accept_3_3 107 172 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 172 280 2 53 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 172 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710
  105 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 172 280 4 26 43 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 172 280
  (Polychromatic418967fa.accept_16_7_12_8_1_2450 103 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 172 280 2 51 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 172 280 (accept_3_3 101 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 172 280 4 25 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 172 280 (Polychromatic418967fa.accept_13_8_3_7_1_2455 99 172 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 172 280 2 49 86 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 172 280
  (Polychromatic418967fa.accept_11_9_7_5_1_749 97 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 172 280 4 24 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 172 280 (accept_3_3 95 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 172 280 2 47 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 172 280 (Polychromatic418967fa.accept_15_3_7_10_1_2324 93 172 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 172 280 4 23 43 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 172 280
  (Polychromatic418967fa.accept_15_1_7_10_1_287 91 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 172 280 2 45 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 172 280 (accept_3_3 89 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 172 280 4 22 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 172 280 (Polychromatic418967fa.accept_13_9_3_7_1_1065 87 172 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 172 280 2 43 86 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 172 280
  (Polychromatic418967fa.accept_16_5_12_8_1_2521 85 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 172 280 4 21 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 172 280 (accept_3_3 83 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 172 280 2 41 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 172 280 (Polychromatic418967fa.accept_16_1_12_8_1_2405 81 172 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 172 280 4 20 43 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 172 280
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 79 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 172 280 2 39 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 172 280 (accept_3_3 77 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 172 280 4 19 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 172 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 75 172 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 172 280 2 37 86 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 172 280
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 73 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 172 280 4 18 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 172 280 (accept_3_3 71 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 172 280 2 35 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 172 280 (Polychromatic418967fa.accept_13_4_3_7_1_2515 69 172 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 172 280 4 17 43 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 172 280
  (Polychromatic418967fa.accept_16_3_12_8_1_808 67 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 172 280 2 33 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 172 280 (accept_3_3 65 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 172 280 4 16 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 172 280 (Polychromatic418967fa.accept_13_11_3_7_1_2513 63 172 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 172 280 2 31 86 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 172 280
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 61 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 172 280 4 15 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 172 280 (accept_3_3 59 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 172 280 2 29 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 172 280 (Polychromatic418967fa.accept_15_12_7_10_1_3297 57 172 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 172 280 4 14 43 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 172 280
  (Polychromatic418967fa.accept_16_7_12_8_1_2450 55 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 172 280 2 27 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 172 280 (accept_3_3 53 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 172 280 4 13 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 172 280 (Polychromatic418967fa.accept_16_3_12_8_1_808 51 172 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 172 280 2 25 86 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 172 280
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 49 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 172 280 4 12 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 172 280 (accept_3_3 47 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 172 280 2 23 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 172 280 (Polychromatic418967fa.accept_16_13_12_8_1_2451 45 172 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 172 280 4 11 43 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 172 280
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 43 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 172 280 2 21 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 172 280 (accept_3_3 41 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 172 280 4 10 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 172 280 (Polychromatic418967fa.accept_16_7_12_8_1_2450 39 172 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 280 2 19 86 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 280
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 280 4 9 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 172 280 (accept_3_3 35 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  172 280 2 17 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 172 280 (Polychromatic418967fa.accept_15_3_7_10_1_2324 33 172 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 280 4 8 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 280 (Polychromatic418967fa.accept_11_9_7_5_1_749
  31 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 172 280 2 15 86 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 172 280
  (accept_3_3 29 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 172 280 4 7 43 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 172 280
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 172 280 2 13 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 172 280 (Polychromatic418967fa.accept_16_9_12_8_1_1554 25 172 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 172 280 4 6 43 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 172 280 (accept_3_3 23 172 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 172 280 2 11 86 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 172 280
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 172 280 4 5 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 172 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 172 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 172 280 2 9 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 172 280 (accept_3_3 17 172 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 172 280 4 4 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 172 280 (Polychromatic418967fa.accept_16_15_12_8_1_4585 15 172
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 280 2 7 86 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 280
  (Polychromatic418967fa.accept_16_13_12_8_1_2451 13 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 172 280 4 3 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 172 280 (accept_3_3 11 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 172 280 2 5 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 172 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 172 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 280 4 2 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 280 (Polychromatic418967fa.accept_16_7_12_8_1_2450
  7 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 280 2 3 86 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 280 (accept_3_3 5
  172 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172 280 4 1 43 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 172 280
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 3 172 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 172 280 2 1 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 172 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 172 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 172
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 171 280 (Eq.refl Bool.true) (allA_succ_of_accept 109 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  109 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 171 280
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 108 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 171 280 (accept_3_3 107 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 171 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 106 171 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 171 280 (Polychromatic418967fa.accept_18_15_9_10_1_1082 105
  171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 171 280 (accept_3_3 104
  171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 171 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 103 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 171 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 102 171 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 171 280 (accept_3_3 101 171 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 171 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 100 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 171 280
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 99 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 171 280 (accept_3_3 98 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 171 280 (Polychromatic418967fa.accept_13_5_2_7_1_2414 96 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 171 280 (accept_3_3 95 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 171 280 (Polychromatic418967fa.accept_15_4_6_10_1_823 94 171
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 171 280
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 93 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 171 280 (accept_3_3 92 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 171 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 90 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 171 280 (accept_3_3 89 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 171 280 (Polychromatic418967fa.accept_21_4_3_7_1_11420 88 171
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 171 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 87 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 171 280 (accept_3_3 86 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 171 280 (Polychromatic418967fa.accept_16_4_11_8_1_1574 84 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 171 280 (accept_3_3 83 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 171 280 (Polychromatic418967fa.accept_23_13_10_4_1_12534 82
  171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 171 280
  (Polychromatic418967fa.accept_22_15_17_16_1_17209 81 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 171 280 (accept_3_3 80 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 171 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 171 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 78 171
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 171 280 (accept_3_3 77 171
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 171 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 76 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 171 280 (Polychromatic418967fa.accept_17_7_1_8_1_6280 75 171 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 171 280 (accept_3_3 74 171 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 171 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 171 280
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 72 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 171 280 (accept_3_3 71 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 171 280 (Polychromatic418967fa.accept_13_5_2_7_1_2414 70 171 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 171 280 (Polychromatic418967fa.accept_16_5_11_8_1_3431 69 171
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 171 280 (accept_3_3 68 171
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  67 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 171 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 171 280 (accept_3_3 65 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 171 280 (Polychromatic418967fa.accept_15_4_6_10_1_823 64 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 171 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539 63 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 171 280 (accept_3_3 62 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 171 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 171 280
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 60 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 171 280 (accept_3_3 59 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 171 280 (Polychromatic418967fa.accept_17_7_1_8_1_6280 58 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 171 280 (Polychromatic418967fa.accept_13_5_2_7_1_2414 57 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 171 280 (accept_3_3 56 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 171 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 171 280 (accept_3_3 53 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 171 280 (Polychromatic418967fa.accept_16_4_11_8_1_1574 52 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 171 280 (Polychromatic418967fa.accept_16_3_11_8_1_830 51 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 280 (accept_3_3 50 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 171 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 280
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 48 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 171 280 (accept_3_3 47 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 171 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 171 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 280 (accept_3_3 44 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 171 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 171 280 (accept_3_3 41 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 171 280 (Polychromatic418967fa.accept_22_18_17_16_1_4598 40 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 280 (Polychromatic418967fa.accept_23_16_10_4_1_17208 39 171 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 280 (accept_3_3 38 171 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37
  171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 280
  (Polychromatic418967fa.accept_16_4_11_8_1_1574 36 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 171 280 (accept_3_3 35 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 171 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 34 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 171 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 280 (accept_3_3 32 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 171 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 171 280 (accept_3_3 29 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 171 280 (Polychromatic418967fa.accept_16_12_11_8_1_832 28 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 171 280 (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 280 (accept_3_3 26 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 171 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 280
  (Polychromatic418967fa.accept_17_7_1_8_1_6280 24 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 171 280 (accept_3_3 23 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 171 280 (Polychromatic418967fa.accept_13_9_2_7_1_1083 22 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 171 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 280 (accept_3_3 20 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 171 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 171 280 (accept_3_3 17 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 171 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 16 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 171 280 (Polychromatic418967fa.accept_18_15_9_10_1_1082 15 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 280 (accept_3_3 14 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 171 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 280
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 171 280 (accept_3_3 11 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 171 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 171 280 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 171 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 280 (accept_3_3 8 171 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 171 280 (accept_3_3 5 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  171 280 (Polychromatic418967fa.accept_15_4_6_10_1_823 4 171 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 171 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 280 (accept_3_3 2 171 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 171 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 170 280 (Eq.refl Bool.true) (allA_of_3_1 111 170 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 112 169 280 (Eq.refl Bool.true) (allA_succ_of_accept 111 169 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 169 280 (accept_3_3 110 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 169 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 109 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 169 280 (Polychromatic418967fa.accept_16_12_9_8_1_2508 108 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 169 280 (accept_3_3 107 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 169 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 106 169
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 169 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 169 280 (accept_3_3 104 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 169 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 103 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 169 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 102 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 169 280 (accept_3_3 101 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 169 280 (Polychromatic418967fa.accept_16_4_9_8_1_2509 100 169
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 169 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 169 280 (accept_3_3 98 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 169 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 97 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 169 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 96 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 169 280 (accept_3_3 95 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 169 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 94 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 169 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 169 280 (accept_3_3 92 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 169 280 (Polychromatic418967fa.accept_19_15_17_14_1_1370 91 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 169 280 (Polychromatic418967fa.accept_21_6_1_7_1_11405 90 169 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 169 280 (accept_3_3 89 169 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 169 280
  (Polychromatic418967fa.accept_15_13_4_10_1_821 88 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 169 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 169 280 (accept_3_3 86 169 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 169 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 169 280 (Polychromatic418967fa.accept_9_3_7_1_1_143
  84 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 169 280 (accept_3_3 83
  169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 169 280
  (Polychromatic418967fa.accept_12_10_1_4_1_392 82 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 169 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 169 280 (accept_3_3 80 169 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 169 280 (Polychromatic418967fa.accept_16_15_9_8_1_2440 79 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 169 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 169 280 (accept_3_3 77 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 169 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 169 280 (accept_3_3 74 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 169 280 (Polychromatic418967fa.accept_15_13_4_10_1_821 73 169 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 169 280
  (Polychromatic418967fa.accept_19_15_17_14_1_1370 72 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 169 280 (accept_3_3 71 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 169 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 169 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 169 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 169 280 (accept_3_3 68 169 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 169 280 (Polychromatic418967fa.accept_9_4_7_1_1_379
  67 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 169 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 169 280 (accept_3_3 65 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 169 280 (Polychromatic418967fa.accept_23_18_8_4_1_17207 64 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 169 280 (accept_3_3 62 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 169 280 (Polychromatic418967fa.accept_21_19_1_7_1_3724 61 169 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 169 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 169 280 (accept_3_3 59 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 169 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 169 280 (accept_3_3 56 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 169 280 (Polychromatic418967fa.accept_16_7_9_8_1_829 55 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 169 280
  (Polychromatic418967fa.accept_11_10_4_5_1_359 54 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 169 280 (accept_3_3 53 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 169 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 52 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 280 (accept_3_3 50 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 169 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 169 280 (accept_3_3 47 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 169 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 280 (accept_3_3 44 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 169 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 43 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 169 280 (accept_3_3 41 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 169 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 280 (accept_3_3 38 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 169 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 37 169 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 280
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 36 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 169 280 (accept_3_3 35 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 169 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 280 (accept_3_3 32 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 280 (accept_3_3 29 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 280 (Polychromatic418967fa.accept_15_13_4_10_1_821 28 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 280 (accept_3_3 26 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 280 (Polychromatic418967fa.accept_21_4_1_7_1_3771 25 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 280 (accept_3_3 23 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 280 (accept_3_3 20 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 280 (Polychromatic418967fa.accept_17_2_16_8_1_3881 19 169 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 280
  (Polychromatic418967fa.accept_23_18_8_4_1_17207 18 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 169 280 (accept_3_3 17 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 169 280 (Polychromatic418967fa.accept_19_16_17_14_1_4969 16 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15
  169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 280 (accept_3_3 14
  169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 169 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 169 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 280 (accept_3_3 11 169 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 169 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 280 (accept_3_3 8 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 280 (accept_3_3 5 169 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 169 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 280 (accept_3_3 2 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 280 (Polychromatic418967fa.accept_16_1_9_8_1_2438 1 169 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 168 280 (Eq.refl Bool.true) (allA_succ_of_gcd 112 168 280 56 2 3 5 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 168 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 111 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 168 280 2 55 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 168 280 (Polychromatic418967fa.accept_13_5_12_7_1_1080 109 168 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 168 280 4 27 42 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 168 280 (accept_3_3 107 168 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 168 280 2 53 84 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 168 280 7 15 24 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 168 280 8 13 21 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 168 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 103 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 168 280 2 51 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 168 280 (accept_3_3 101 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 168 280 4 25 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 168 280 (Polychromatic418967fa.accept_13_8_12_7_1_2442 99 168 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 168 280 14 7 12 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 168 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 97 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 168 280 8 12 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 168 280 (accept_3_3 95 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 168 280 2 47 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 168 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 168 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 168 280 4 23 42 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 91 168 280 7 13 24 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 90 168 280 2 45 84 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 168 280 (accept_3_3 89
  168 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 168 280 8 11 21 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 168 280
  (Polychromatic418967fa.accept_18_15_6_10_1_5590 87 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 168 280 2 43 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 168 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 85 168 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 168 280 28 3 6 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 168 280 (accept_3_3 83 168 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 168 280 2 41 84 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 168 280
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 81 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 168 280 8 10 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 168 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 79 168 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 168 280 2 39 84 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 168 280 7 11 24 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 168 280 4 19 42 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 168 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 75 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 168 280 2 37 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 168 280 (Polychromatic418967fa.accept_13_8_12_7_1_2442 73 168 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 168 280 8 9 21 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 168 280 (accept_3_3 71 168 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 168 280 14 5 12 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 168 280
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 69 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 168 280 4 17 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 168 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 168 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 168 280 2 33 84 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 168 280 (accept_3_3 65 168 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 168 280 8 8 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 168 280 7 9 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 168 280 2 31 84 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 168 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 61 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 280 4 15 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 280 (accept_3_3 59 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 168 280 2 29 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 168 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 168 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 168 280 56 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 280
  (Polychromatic418967fa.accept_19_17_16_14_1_10604 55 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 168 280 2 27 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 168 280 (accept_3_3 53 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 168 280 4 13 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 168 280 (Polychromatic418967fa.accept_15_6_3_10_1_2341 51 168 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 168 280 2 25 84 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 168 280 7 7 24 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 168 280 8 6 21 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 168 280 (accept_3_3 47 168 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 280 2 23 84 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 168 280
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 168 280 4 11 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 168 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 168 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 168 280 14 3 12 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 168 280 (accept_3_3 41 168 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 280 8 5 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 168 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39
  168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 168 280 2 19 84 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 280
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 168 280 4 9 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 168 280 7 5 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 34 168 280 2 17 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 280 (Polychromatic418967fa.accept_18_15_6_10_1_5590 33 168
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 168 280 8 4 21 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 280 2 15 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 280 (accept_3_3 29 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 280 28 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 168 280 (Polychromatic418967fa.accept_17_10_15_8_1_6324 27 168 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 168 280 2 13 84 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 280 8 3 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 168 280 (accept_3_3 23 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  168 280 2 11 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  21 168 280 7 3 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  20 168 280 4 5 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 168 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 168 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 280 2 9 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 280 (accept_3_3 17 168 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 280 8 2 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 280 (Polychromatic418967fa.accept_18_15_6_10_1_5590 15 168
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 168 280 14 1 12 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 280 4 3 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 168 280 (accept_3_3 11 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  168 280 2 5 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 168 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 168 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 168 280 8 1 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 168 280 7 1 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 168 280 2 3 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 280 (accept_3_3 5 168 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 168 280 4 1 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 168 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 168 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 280 2 1 84 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 280
  (Polychromatic418967fa.accept_25_1_18_5_1_17206 1 168 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 167 280 (Eq.refl Bool.true) (allA_of_3_1 114 167 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 115 166 280 (Eq.refl Bool.true) (allA_succ_of_gcd 114 166 280 2 57 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 166 280 (accept_3_3 113 166 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 166 280 2 56 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 166 280 (Polychromatic418967fa.accept_9_3_4_1_1_22
  111 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 166 280 2 55 83 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 166 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 109 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 166 280 2 54 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 166 280 (accept_3_3 107 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 166 280 2 53 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 166 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 105 166 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 166 280 2 52 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 166 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 103 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 166 280 2 51 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 166 280 (accept_3_3 101 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 166 280 2 50 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 166 280 (Polychromatic418967fa.accept_13_8_10_7_1_1702 99 166 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 166 280 2 49 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 166 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 97 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 166 280 2 48 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 166 280 (accept_3_3 95 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 166 280 2 47 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 166 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 93 166 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 166 280 2 46 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 166 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 91 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 166 280 2 45 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 166 280 (accept_3_3 89 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 166 280 2 44 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 166 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 87 166 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 166 280 2 43 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 166 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 166 280 2 42 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 166 280 (accept_3_3 83 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 166 280 2 41 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 166 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 81 166 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 166 280 2 40 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 166 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 79 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 166 280 2 39 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 166 280 (accept_3_3 77 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 166 280 2 38 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 166 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 75 166 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 166 280 2 37 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 166 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 166 280 2 36 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 166 280 (accept_3_3 71 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 166 280 2 35 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 166 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 166 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 166 280 2 34 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 166 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 166 280 2 33 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 166 280 (accept_3_3 65 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 166 280 2 32 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 166 280 (Polychromatic418967fa.accept_22_19_12_16_1_6241 63 166 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 166 280 2 31 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 166 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 61 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 166 280 2 30 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 166 280 (accept_3_3 59 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 166 280 2 29 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 166 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 166 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 166 280 2 28 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 166 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 166 280 2 27 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 166 280 (accept_3_3 53 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 280 2 26 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 166 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 280 2 25 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 166 280 2 24 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 166 280 (accept_3_3 47 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 280 2 23 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 280 (Polychromatic418967fa.accept_22_1_12_16_1_6178 45 166 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 280 2 22 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 280 2 21 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 280 (accept_3_3 41 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 280 2 20 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 166 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 280 2 19 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 280 2 18 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 280 (accept_3_3 35 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 280 2 17 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 166 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 280 2 16 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 166 280 2 15 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 166 280 (accept_3_3 29 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 280 2 14 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 280 (Polychromatic418967fa.accept_22_5_12_16_1_15745 27 166 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 280 2 13 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 280 2 12 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 280 (accept_3_3 23 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 280 2 11 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 166 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 280 2 10 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 280 2 9 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 280 (accept_3_3 17 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 280 2 8 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 166 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 280 2 7 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 166 280 2 6 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 166 280 (accept_3_3 11 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 280 2 5 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 280 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 166 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 280 2 4 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 280 2 3 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 280 (accept_3_3 5 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  280 2 2 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 166 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 280 2 1 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 166 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 165 280 (Eq.refl Bool.true) (allA_succ_of_gcd 115 165 280 5 23 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 114 165 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 114 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 165 280 (accept_3_3 113 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 165 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 112 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 165 280 (Polychromatic418967fa.accept_19_16_13_14_1_3616 111 165 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 165 280 5 22 33 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 165 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 109 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 165 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 108 165 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 165 280 (accept_3_3 107 165 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 165 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 106 165 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 165 280 5 21 33 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 165 280 (accept_3_3 104 165 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  103 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 165 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 102 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 165 280 (accept_3_3 101 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  100 165 280 5 20 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 99 165 280 (Polychromatic418967fa.accept_13_8_9_7_1_530 99 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 165 280 (accept_3_3 98 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 165 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 165 280 (Polychromatic418967fa.accept_9_6_3_1_1_155
  96 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 165 280 5 19 33 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 165 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 94 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 165 280 (Polychromatic418967fa.accept_13_2_9_7_1_164 93 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 165 280 (accept_3_3 92 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 165 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 165 280 5 18 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 165 280 (accept_3_3 89 165 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 165 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 88 165 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 165 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 87 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 165 280 (accept_3_3 86 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  165 280 5 17 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 165 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430 84 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 165 280 (accept_3_3 83 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 165 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 82 165 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 165 280
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 81 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 165 280 5 16 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 165 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 165 280 (Polychromatic418967fa.accept_9_6_3_1_1_155
  78 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 165 280 (accept_3_3 77
  165 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 165 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 76 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 165 280 5 15 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 165 280 (accept_3_3 74 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 165 280 (Polychromatic418967fa.accept_17_4_12_8_1_3833 72 165
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 165 280 (accept_3_3 71 165
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 165 280 5 14 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 165 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 69 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 165 280 (accept_3_3 68 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 165 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 165 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 165 280 5 13 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 165 280
  (Polychromatic418967fa.accept_22_20_11_16_1_6236 64 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 165 280 (Polychromatic418967fa.accept_13_11_9_7_1_2484 63 165 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 165 280 (accept_3_3 62 165 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 165 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 165 280 5 12 33 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 165 280 (accept_3_3 59
  165 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 58 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 165 280 (Polychromatic418967fa.accept_21_15_18_7_1_5161 57 165 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 165 280 (accept_3_3 56 165 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 55 165 280 5 11 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 165 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 165 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 280 (accept_3_3 53 165 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 280 (Polychromatic418967fa.accept_9_7_3_1_1_386
  52 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 165 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 165 280 5 10 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 165 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 280
  (Polychromatic418967fa.accept_21_6_18_7_1_3764 48 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 165 280 (accept_3_3 47 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 165 280 (Polychromatic418967fa.accept_19_8_13_14_1_2373 46 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 165 280 5 9 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 165 280 (accept_3_3 44 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 165 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 280 (accept_3_3 41 165 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 165 280 5 8 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 165 280
  (Polychromatic418967fa.accept_17_5_12_8_1_6304 39 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 165 280 (accept_3_3 38 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 165 280 (Polychromatic418967fa.accept_16_4_5_8_1_2425 36 165 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 165 280 5 7 33 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 165 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 34 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 165 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 280 (accept_3_3 32 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 165 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 280 5 6 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 280 (accept_3_3 29 165 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 280 (Polychromatic418967fa.accept_13_2_9_7_1_164 28 165
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 280
  (Polychromatic418967fa.accept_16_11_5_8_1_2427 27 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 165 280 (accept_3_3 26 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  165 280 5 5 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 165 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 165 280 (accept_3_3 23 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 280 (Polychromatic418967fa.accept_13_8_9_7_1_530 21 165
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 165 280 5 4 33 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 165 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 165 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 280 (accept_3_3 17 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 165 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 165 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 280 5 3 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 280 (accept_3_3 14 165 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 165 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 280
  (Polychromatic418967fa.accept_16_12_5_8_1_2492 12 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 165 280 (accept_3_3 11 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  165 280 5 2 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 165 280 (Polychromatic418967fa.accept_21_9_18_7_1_5180 9 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 165 280 (accept_3_3 8 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 165 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 165 280 5 1 33 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 165 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 4 165 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 165 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 280 (accept_3_3 2 165 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 165 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 165 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 164 280 (Eq.refl Bool.true) (allA_of_3_1 117 164 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 118 163 280 (Eq.refl Bool.true) (allA_succ_of_accept 117 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 163 280 (accept_3_3 116 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 163 280 (Polychromatic418967fa.accept_21_10_16_7_1_11388 115 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 163 280 (Polychromatic418967fa.accept_17_12_10_8_1_5039 114 163 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 163 280 (accept_3_3 113 163 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 163 280
  (Polychromatic418967fa.accept_19_17_11_14_1_7858 112 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 163 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 111 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 163 280 (accept_3_3 110 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 163 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 109
  163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 163 280
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 108 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 163 280 (accept_3_3 107 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 163 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 106 163 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 163 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 105 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 163 280 (accept_3_3 104 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 163 280
  (Polychromatic418967fa.accept_18_13_1_10_1_4331 103 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 163 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 102 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 163 280 (accept_3_3 101 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 163 280 (Polychromatic418967fa.accept_16_4_3_8_1_2486 100 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 163 280 (accept_3_3 98 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 163 280 (Polychromatic418967fa.accept_17_12_10_8_1_5039 97 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 163 280 (Polychromatic418967fa.accept_21_12_16_7_1_14243 96 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 163 280 (accept_3_3 95 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 163 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 94 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 163 280 (accept_3_3 92 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 163 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 91 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 163 280 (Polychromatic418967fa.accept_21_6_16_7_1_3714 90 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 163 280 (accept_3_3 89 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 163 280 (Polychromatic418967fa.accept_18_16_1_10_1_2029 88 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 163 280 (accept_3_3 86 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 163 280 (Polychromatic418967fa.accept_16_5_3_8_1_4555 85 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 163 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 84 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 163 280 (accept_3_3 83 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 163 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 82 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 163 280 (accept_3_3 80 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 163 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 79 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 163 280 (Polychromatic418967fa.accept_15_3_13_10_1_2332 78 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 163 280 (accept_3_3 77 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 163 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 76 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 163 280 (accept_3_3 74 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 163 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 73 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 163 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 72 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 163 280 (accept_3_3 71 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 163 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 163 280 (accept_3_3 68 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 163 280 (Polychromatic418967fa.accept_18_13_1_10_1_4331 67 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 163 280 (Polychromatic418967fa.accept_17_15_10_8_1_1708 66 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 280 (accept_3_3 65 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 64 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 163 280 (accept_3_3 62 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 163 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 61 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 163 280 (Polychromatic418967fa.accept_16_12_3_8_1_5729 60 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 163 280 (accept_3_3 59 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 163 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 163 280 (accept_3_3 56 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 163 280 (Polychromatic418967fa.accept_19_17_11_14_1_7858 55 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 280 (Polychromatic418967fa.accept_19_16_11_14_1_3608 54 163 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 163 280 (accept_3_3 53 163 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 163 280 (Polychromatic418967fa.accept_16_4_3_8_1_2486
  52 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 163 280 (accept_3_3 50 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 163 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 163 280 (Polychromatic418967fa.accept_15_3_13_10_1_2332 48 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 280 (accept_3_3 47 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 280 (accept_3_3 44 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 280 (Polychromatic418967fa.accept_16_11_3_8_1_4597 43 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 42 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 280 (accept_3_3 41 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 40 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 280 (accept_3_3 38 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 280 (Polychromatic418967fa.accept_16_5_3_8_1_4555 37 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 280 (Polychromatic418967fa.accept_16_4_3_8_1_2486 36 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 280 (accept_3_3 35 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 280 (accept_3_3 32 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 280 (Polychromatic418967fa.accept_21_9_16_7_1_5222 30 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 280 (accept_3_3 29 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 280 (Polychromatic418967fa.accept_16_12_3_8_1_5729 28 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 280 (accept_3_3 26 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 280 (Polychromatic418967fa.accept_19_6_11_14_1_10624 25 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 280 (Polychromatic418967fa.accept_19_5_11_14_1_3654 24 163 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 280 (accept_3_3 23 163 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 280 (Polychromatic418967fa.accept_12_10_7_4_1_820
  22 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 280 (accept_3_3 20 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 280 (accept_3_3 17 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 280 (accept_3_3 14 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 280 (Polychromatic418967fa.accept_16_13_3_8_1_2422 13 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 12 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 280 (accept_3_3 11 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 280 (accept_3_3 8 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 280 (Polychromatic418967fa.accept_19_6_11_14_1_10624 6 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 280 (accept_3_3 5 163 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 163
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 280 (accept_3_3 2 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 163 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 162 280 (Eq.refl Bool.true) (allA_succ_of_gcd 118 162 280 2 59 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 162 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 117 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 162 280 2 58 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 162 280 (Polychromatic418967fa.accept_19_1_10_14_1_3597 115 162 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 162 280 2 57 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 162 280 (accept_3_3 113 162 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 162 280 2 56 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 162 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 111 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 162 280 2 55 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 162 280 (Polychromatic418967fa.accept_25_9_12_5_1_6535 109 162 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 162 280 2 54 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 162 280 (accept_3_3 107 162 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 162 280 2 53 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 162 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 105 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 162 280 2 52 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 162 280 (Polychromatic418967fa.accept_13_12_6_7_1_1071 103 162 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 162 280 2 51 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 162 280 (accept_3_3 101 162 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 162 280 2 50 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 162 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 99 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 162 280 2 49 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 162 280 (Polychromatic418967fa.accept_15_7_12_10_1_4335 97 162 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 162 280 2 48 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 162 280 (accept_3_3 95 162 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 162 280 2 47 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 162 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 93 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 162 280 2 46 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 162 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 91 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 162 280 2 45 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 162 280 (accept_3_3 89 162 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 162 280 2 44 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 162 280 (Polychromatic418967fa.accept_12_3_6_4_1_400
  87 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 162 280 2 43 81 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 162 280
  (Polychromatic418967fa.accept_21_1_15_7_1_6775 85 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 162 280 2 42 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 162 280 (accept_3_3 83 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 162 280 2 41 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 162 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 162 280 2 40 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 162 280
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 79 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 162 280 2 39 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 162 280 (accept_3_3 77 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 162 280 2 38 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 162 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 75 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 162 280 2 37 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 162 280
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 73 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 162 280 2 36 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 162 280 (accept_3_3 71 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 162 280 2 35 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 162 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 69 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 162 280 2 34 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 162 280
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 67 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 162 280 2 33 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 162 280 (accept_3_3 65 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 162 280 2 32 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 162 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 162 280 2 31 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 280
  (Polychromatic418967fa.accept_13_9_6_7_1_551 61 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 280 2 30 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 280 (accept_3_3 59 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 162 280 2 29 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 162 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 162 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 162 280 2 28 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 280
  (Polychromatic418967fa.accept_21_13_15_7_1_5209 55 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 162 280 2 27 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 162 280 (accept_3_3 53 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 162 280 2 26 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 162 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 162 280 2 25 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 280
  (Polychromatic418967fa.accept_23_3_1_4_1_17205 49 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 280 2 24 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 280 (accept_3_3 47 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 162 280 2 23 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 162 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 162 280 2 22 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 280
  (Polychromatic418967fa.accept_13_4_6_7_1_2471 43 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 280 2 21 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 280 (accept_3_3 41 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 162 280 2 20 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 162 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 162 280 2 19 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 280
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 37 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 162 280 2 18 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 162 280 (accept_3_3 35 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 162 280 2 17 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 162 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 162 280 2 16 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 280
  (Polychromatic418967fa.accept_19_12_10_14_1_6353 31 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 162 280 2 15 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 162 280 (accept_3_3 29 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 162 280 2 14 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 162 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 162 280 2 13 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 25 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 280 2 12 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 280 (accept_3_3 23 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 162 280 2 11 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 162 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 162 280 2 10 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 280
  (Polychromatic418967fa.accept_21_19_15_7_1_3709 19 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 162 280 2 9 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 162 280 (accept_3_3 17 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 162 280 2 8 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 162 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 162 280 2 7 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 280
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 280 2 6 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 280 (accept_3_3 11 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 280 2 5 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 162 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 162 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 280 2 4 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 280
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 280 2 3 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 280 (accept_3_3 5 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162
  280 2 2 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  162 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 162 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 162 280 2 1 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 162 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 162 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 161 280 (Eq.refl Bool.true) (allA_of_3_1 120 161 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 121 160 280 (Eq.refl Bool.true) (allA_succ_of_gcd 120 160 280 40 3 4 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 160 280 (accept_3_3 119 160 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 160 280 2 59 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 160 280
  (Polychromatic418967fa.accept_19_3_8_14_1_14571 117 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 160 280 4 29 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 115 160 280 5 23 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 114 160 280 2 57 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 160 280 (accept_3_3 113 160 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 112 160 280 8 14 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 160 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 111 160
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 160 280 10 11 16 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 160 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 109 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 160 280 4 27 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 160 280 (accept_3_3 107 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 160 280 2 53 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 160 280 5 21 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 160 280 8 13 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 160 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 103 160
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 160 280 2 51 80 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 160 280 (accept_3_3
  101 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 160 280 20 5 8 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 160 280
  (Polychromatic418967fa.accept_17_14_7_8_1_7544 99 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 160 280 2 49 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 160 280 (Polychromatic418967fa.accept_13_6_4_7_1_2464 97 160 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 160 280 8 12 20 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 160 280 5 19 32 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 160 280 2 47 80 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 160 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 93 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 160 280 4 23 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 160 280 (Polychromatic418967fa.accept_18_1_16_10_1_2065 91 160 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 160 280 10 9 16 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 160 280 (accept_3_3 89 160 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 160 280 8 11 20 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 160 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 87 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 160 280 2 43 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 160 280 5 17 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 160 280 4 21 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 160 280 (accept_3_3 83 160 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 160 280 2 41 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 160 280 (Polychromatic418967fa.accept_13_3_4_7_1_1711 81 160 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 160 280 40 2 4 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 160 280
  (Polychromatic418967fa.accept_19_3_8_14_1_14571 79 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 160 280 2 39 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 160 280 (accept_3_3 77 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 160 280 4 19 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 160 280 5 15 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 160 280 2 37 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 160 280 (Polychromatic418967fa.accept_18_1_16_10_1_2065 73 160
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 160 280 8 9 20 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 160 280 (accept_3_3 71
  160 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 160 280 10 7 16 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 160 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 69 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 160 280 4 17 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 160 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 160 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 160 280 2 33 80 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 160 280 5 13 32 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 160 280 8 8 20 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 160 280
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 63 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 160 280 2 31 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 160 280 (Polychromatic418967fa.accept_13_9_4_7_1_1694 61 160 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 160 280 20 3 8 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 160 280 (accept_3_3 59 160 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 160 280 2 29 80 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 160 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 57 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 160 280 8 7 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 160 280 5 11 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 160 280 2 27 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 160 280 (accept_3_3 53 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 160 280 4 13 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 160 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 160 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 280 10 5 16 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 160 280 8 6 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 160 280 (accept_3_3 47 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  160 280 2 23 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  45 160 280 5 9 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  44 160 280 4 11 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 160 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 160 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 160 280 2 21 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 160 280 (accept_3_3 41 160 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 160 280 40 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 160 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 160 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 280 2 19 80 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 280
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 160 280 4 9 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 160 280 5 7 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 160 280 2 17 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 160 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 160 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 160 280 8 4 20 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 160 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 160 280 10 3 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 160 280 (accept_3_3 29 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 160 280 4 7 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 160 280 (Polychromatic418967fa.accept_21_6_13_7_1_8394 27 160 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 280 2 13 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 160 280 5 5 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 160 280 8 3 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 160 280 (accept_3_3 23 160 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 160 280 2 11 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 160 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 160 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 280 20 1 8 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 280
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 160 280 2 9 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 160 280 (accept_3_3 17 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 160 280 8 2 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 160 280 5 3 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 160 280 2 7 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 160 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 160 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 160 280 4 3 40 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 160 280 (accept_3_3 11 160 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 280 10 1 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 280 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9
  160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 280 8 1 20 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 280
  (Polychromatic418967fa.accept_19_7_8_14_1_13273 7 160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 160 280 2 3 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 160 280 5 1 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 160 280 4 1 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 160 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 160 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 280 2 1 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1
  160 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 159 280 (Eq.refl Bool.true) (allA_succ_of_accept 121 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  121 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 159 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 120 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 159 280 (accept_3_3 119 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 159 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 118 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 159 280 (Polychromatic418967fa.accept_15_12_9_10_1_2326 117 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 159 280 (accept_3_3 116 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 159 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 114 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 159 280 (accept_3_3 113 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 159 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 112 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 159 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 111 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 159 280 (accept_3_3 110 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 159 280
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 108 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 159 280 (accept_3_3 107 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 159 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 106 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 159 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 105 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 159 280 (accept_3_3 104 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 159 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 102 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 159 280 (accept_3_3 101 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 159 280 (Polychromatic418967fa.accept_13_9_3_7_1_1065 100 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 159 280 (Polychromatic418967fa.accept_13_8_3_7_1_2455 99 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 159 280 (accept_3_3 98 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 159 280
  (Polychromatic418967fa.accept_18_6_15_10_1_6975 96 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 159 280 (accept_3_3 95 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 159 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 94 159 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 159 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 159 280 (accept_3_3 92 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91
  159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 159 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 90 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 159 280 (accept_3_3 89 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 159 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 88 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 159 280 (Polychromatic418967fa.accept_13_9_3_7_1_1065 87 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 159 280 (accept_3_3 86 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 159 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 159 280 (accept_3_3 83 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 159 280 (Polychromatic418967fa.accept_13_4_3_7_1_2515 82 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 159 280 (Polychromatic418967fa.accept_16_1_15_8_1_2411 81 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 159 280 (accept_3_3 80 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 159 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 78 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 159 280 (accept_3_3 77 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 159 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 159 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 159 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 159 280 (accept_3_3 74 159 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 159 280
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 72 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 159 280 (accept_3_3 71 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 159 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 159 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 159 280 (Polychromatic418967fa.accept_13_4_3_7_1_2515 69 159
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 280 (accept_3_3 68 159
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  67 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 159 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 159 280 (accept_3_3 65 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 159 280 (Polychromatic418967fa.accept_15_4_9_10_1_5384 64 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 159 280 (Polychromatic418967fa.accept_13_11_3_7_1_2513 63 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 280 (accept_3_3 62 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 280
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 60 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 159 280 (accept_3_3 59 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 159 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 159 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 159 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 280 (accept_3_3 56 159 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 159 280 (accept_3_3 53 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 159 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 159 280 (Polychromatic418967fa.accept_22_7_5_16_1_17192 51 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 280 (accept_3_3 50 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 159 280 (accept_3_3 47 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 159 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 46 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 159 280 (Polychromatic418967fa.accept_18_9_15_10_1_395 45 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 280 (accept_3_3 44 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 159 280 (accept_3_3 41 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 159 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 159 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 159 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 280 (accept_3_3 38 159 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 280
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 159 280 (accept_3_3 35 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 159 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 159 280 (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 280 (accept_3_3 32 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 159 280 (accept_3_3 29 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 159 280 (Polychromatic418967fa.accept_16_12_15_8_1_4586 28 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 159 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 280 (accept_3_3 26 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 280
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 159 280 (accept_3_3 23 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 159 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 159 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 159 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 280 (accept_3_3 20 159 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 280 (accept_3_3 17 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 280 (Polychromatic418967fa.accept_17_15_6_8_1_6343 15 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 280 (accept_3_3 14 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 159 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 280 (accept_3_3 11 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 280 (Polychromatic418967fa.accept_13_10_3_7_1_2517 10 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 280 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 159 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 280 (accept_3_3 8 159 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 280 (accept_3_3 5 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 159 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 159 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 280 (accept_3_3 2 159 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 159 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 123 158 280 (Eq.refl Bool.true) (allA_of_3_1 123 158 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 124 157 280 (Eq.refl Bool.true) (allA_succ_of_accept 123 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 123 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 157 280 (accept_3_3 122 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 157 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 121 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 157 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 120 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 157 280 (accept_3_3 119 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 157 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 118 157
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 157 280 (accept_3_3 116 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 115 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 157 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 114 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 157 280 (accept_3_3 113 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 157 280 (Polychromatic418967fa.accept_13_8_1_7_1_2505 112 157
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 157 280 (accept_3_3 110 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 157 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 109 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 157 280 (Polychromatic418967fa.accept_15_3_7_10_1_2324 108 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 157 280 (accept_3_3 107 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 106 157
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 157 280 (accept_3_3 104 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 157 280 (Polychromatic418967fa.accept_17_1_4_8_1_5049 103 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 157 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 102 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 157 280 (accept_3_3 101 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 157 280 (Polychromatic418967fa.accept_16_4_13_8_1_3424 100
  157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 157 280 (accept_3_3 98 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 97 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 157 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 96 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 157 280 (accept_3_3 95 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 157 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 94 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 157 280 (accept_3_3 92 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 157 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 91 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 157 280 (Polychromatic418967fa.accept_22_2_3_16_1_15735 90 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 157 280 (accept_3_3 89 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 157 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 157 280 (accept_3_3 86 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 157 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 85 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 157 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 157 280 (accept_3_3 83 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 157 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 157 280 (accept_3_3 80 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 157 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 78 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 157 280 (accept_3_3 77 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 157 280 (Polychromatic418967fa.accept_13_11_1_7_1_1691 76 157 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 157 280 (accept_3_3 74 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 157 280 (Polychromatic418967fa.accept_13_8_1_7_1_2505 73 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 157 280 (Polychromatic418967fa.accept_15_12_7_10_1_3297 72 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 157 280 (accept_3_3 71 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 157 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 157 280 (accept_3_3 68 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 157 280 (Polychromatic418967fa.accept_16_3_13_8_1_1594 67 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 157 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 157 280 (accept_3_3 65 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 157 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 64 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 157 280 (accept_3_3 62 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 157 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 280 (accept_3_3 59 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 157 280 (accept_3_3 56 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 55 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 280 (Polychromatic418967fa.accept_19_16_5_14_1_11928 54 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 280 (accept_3_3 53 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 157 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 280 (accept_3_3 50 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 49 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 280 (accept_3_3 47 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 280 (accept_3_3 44 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 280 (accept_3_3 41 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 280 (Polychromatic418967fa.accept_18_4_13_10_1_2064 40 157 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 280 (accept_3_3 38 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 280 (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 280 (Polychromatic418967fa.accept_16_4_13_8_1_3424 36 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 280 (accept_3_3 35 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 157 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 280 (accept_3_3 32 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 280 (accept_3_3 29 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 280 (Polychromatic418967fa.accept_16_12_13_8_1_2409 28 157 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 280 (accept_3_3 26 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 280 (accept_3_3 23 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 280 (accept_3_3 20 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 280 (Polychromatic418967fa.accept_15_3_7_10_1_2324 18 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 280 (accept_3_3 17 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 157 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 280 (accept_3_3 14 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 280 (Polychromatic418967fa.accept_17_13_4_8_1_3830 13 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 280 (accept_3_3 11 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 280 (accept_3_3 8 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 280 (accept_3_3 5 157 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 157 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 280 (accept_3_3 2 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 157 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 156 280 (Eq.refl Bool.true) (allA_succ_of_gcd 124 156 280 4 31 39 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 156 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 123 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 156 280 2 61 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 156 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 121 156 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 156 280 4 30 39 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 156 280 (accept_3_3 119 156 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 156 280 2 59 78 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 156 280
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 117 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 156 280 4 29 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 156 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 115 156 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 156 280 2 57 78 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 156 280 (accept_3_3 113 156 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 156 280 4 28 39 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 156 280
  (Polychromatic418967fa.accept_16_15_12_8_1_4585 111 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 156 280 2 55 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 156 280 (Polychromatic418967fa.accept_15_4_6_10_1_823 109 156 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 156 280 4 27 39 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 156 280 (accept_3_3
  107 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 156 280 2 53 78 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 156 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 105 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 156 280 4 26 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 156 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 103 156 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 156 280 2 51 78 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 156 280 (accept_3_3 101 156 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 156 280 4 25 39 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 156 280
  (Polychromatic418967fa.accept_16_3_12_8_1_808 99 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 156 280 2 49 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 156 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 97 156 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 156 280 4 24 39 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 156 280 (accept_3_3 95 156 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 156 280 2 47 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 156 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539
  93 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 156 280 4 23 39 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 156 280
  (Polychromatic418967fa.accept_15_1_6_10_1_23 91 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 156 280 2 45 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 156 280 (accept_3_3 89 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 156 280 4 22 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 156 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 156 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 156 280 2 43 78 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 156 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 85 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 156 280 4 21 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 156 280 (accept_3_3 83 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 156 280 2 41 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 156 280 (Polychromatic418967fa.accept_16_1_12_8_1_2405 81 156 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 156 280 4 20 39 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 156 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 79 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 156 280 2 39 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 156 280 (accept_3_3 77 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 156 280 4 19 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 156 280 (Polychromatic418967fa.accept_16_11_12_8_1_1592 75 156 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 156 280 2 37 78 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 156 280
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 73 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 280 4 18 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 280 (accept_3_3 71 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 156 280 2 35 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 156 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 156 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 156 280 4 17 39 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 67 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 280 2 33 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 280 (accept_3_3 65 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 156 280 4 16 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 156 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 156 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 156 280 2 31 78 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 280 4 15 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 280 (accept_3_3 59 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 156 280 2 29 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 156 280 (Polychromatic418967fa.accept_15_12_6_10_1_1516 57 156 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 156 280 4 14 39 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 280
  (Polychromatic418967fa.accept_16_7_12_8_1_2450 55 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 280 2 27 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 280 (accept_3_3 53 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 156 280 4 13 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 156 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 156 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 156 280 2 25 78 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 280 4 12 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 280 (accept_3_3 47 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 156 280 2 23 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 156 280 (Polychromatic418967fa.accept_16_13_12_8_1_2451 45 156 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 156 280 4 11 39 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 280 2 21 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 280 (accept_3_3 41 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 156 280 4 10 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 156 280 (Polychromatic418967fa.accept_16_7_12_8_1_2450 39 156 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 156 280 2 19 78 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 280
  (Polychromatic418967fa.accept_16_5_12_8_1_2521 37 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 280 4 9 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 280 (accept_3_3 35 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  156 280 2 17 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 156 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 156 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 280 4 8 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 31
  156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 280 2 15 78 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 280 (accept_3_3 29
  156 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 280 4 7 39 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 280
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 156 280 2 13 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 156 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 156 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 280 4 6 39 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 280 (accept_3_3 23 156 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 280 2 11 78 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 280
  (Polychromatic418967fa.accept_16_5_12_8_1_2521 21 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 156 280 4 5 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 156 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 156 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 280 2 9 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 280 (accept_3_3 17 156 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 280 4 4 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 156 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 280 2 7 78 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 280 4 3 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 156 280 (accept_3_3 11 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  156 280 2 5 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 156 280 (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 156 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 280 4 2 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 156 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 280 2 3 78 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 280 (accept_3_3 5
  156 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 280 4 1 39 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 156 280
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 156 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 156 280 2 1 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 156 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 1 156 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 156
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 126 155 280 (Eq.refl Bool.true) (allA_of_3_1 126 155 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 127 154 280 (Eq.refl Bool.true) (allA_succ_of_gcd 126 154 280 14 9 11 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 154 280 (accept_3_3 125 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 154 280 2 62 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 154 280 (Polychromatic418967fa.accept_17_4_1_8_1_5070
  123 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 154 280 2 61 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 154 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 121 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 154 280 2 60 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 119 154 280 7 17 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 118 154 280 2 59 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 154 280 (Polychromatic418967fa.accept_23_2_16_4_1_12491 117
  154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 154 280 2 58 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 154 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 115 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 154 280 2 57 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 154 280 (accept_3_3 113 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 154 280 14 8 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 154 280 (Polychromatic418967fa.accept_15_6_4_10_1_2319 111 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 154 280 2 55 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 154 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 109 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 154 280 2 54 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 154 280 (accept_3_3 107 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 154 280 2 53 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 154 280 7 15 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 154 280 2 52 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 154 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 103 154
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 154 280 2 51 77 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 154 280 (accept_3_3
  101 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 154 280 2 50 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 154 280
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 99 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 154 280 14 7 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 154 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 97 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 154 280 2 48 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 154 280 (accept_3_3 95 154 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 154 280 2 47 77 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 154 280
  (Polychromatic418967fa.accept_19_17_2_14_1_11897 93 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 154 280 2 46 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 91 154 280 7 13 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 90 154 280 2 45 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 154 280 (accept_3_3 89 154 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 88 154 280 2 44 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 154 280 (Polychromatic418967fa.accept_13_9_11_7_1_1077 87 154
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 154 280 2 43 77 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 154 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 154 280 14 6 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 154 280 (accept_3_3 83 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 154 280 2 41 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 154 280 (Polychromatic418967fa.accept_13_3_11_7_1_2488 81 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 154 280 2 40 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 154 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 79 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 154 280 2 39 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 154 280 7 11 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 76 154 280 2 38 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 154 280 (Polychromatic418967fa.accept_17_7_1_8_1_6280 75 154
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 154 280 2 37 77 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 154 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 154 280 2 36 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 154 280 (accept_3_3 71 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 154 280 14 5 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 154 280 (Polychromatic418967fa.accept_13_4_11_7_1_558 69 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 154 280 2 34 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 154 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 154 280 2 33 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 154 280 (accept_3_3 65 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 154 280 2 32 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 154 280 7 9 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 62 154 280 2 31 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 154 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 61 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 154 280 2 30 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 154 280 (accept_3_3 59 154 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 154 280 2 29 77 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 154 280
  (Polychromatic418967fa.accept_13_5_11_7_1_559 57 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 154 280 14 4 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 154 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 55 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 154 280 2 27 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 154 280 (accept_3_3 53 154 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 154 280 2 26 77 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 154 280
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 51 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 154 280 2 25 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 49 154 280 7 7 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 48 154 280 2 24 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 154 280 (accept_3_3 47 154 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 154 280 2 23 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 154 280 (Polychromatic418967fa.accept_17_11_1_8_1_7502 45 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 280 2 22 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 154 280 14 3 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 154 280 (accept_3_3 41 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 280 2 20 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 280 (Polychromatic418967fa.accept_15_9_4_10_1_2316 39 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 280 2 19 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 154 280 2 18 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 154 280 7 5 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 154 280 2 17 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 154 280 (Polychromatic418967fa.accept_23_10_16_4_1_4061 33 154 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 280 2 16 77 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 280 2 15 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 280 (accept_3_3 29 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 280 14 2 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 280 2 13 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 280 2 12 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 280 (accept_3_3 23 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 280 2 11 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 154 280 7 3 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 154 280 2 10 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 154 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 154 280 2 9 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 154 280 (accept_3_3 17 154 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 154 280 2 8 77 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 154 280
  (Polychromatic418967fa.accept_23_15_16_4_1_13993 15 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 154 280 14 1 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 154 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 280 2 6 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 154 280 (accept_3_3 11 154 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 154 280 2 5 77 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 280
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 154 280 2 4 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 154 280 7 1 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 154 280 2 3 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 280 (accept_3_3 5 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  280 2 2 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 280 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 154 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 280 2 1 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 154 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 128 153 280 (Eq.refl Bool.true) (allA_succ_of_accept 127 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  127 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 153 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 126 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 153 280 (accept_3_3 125 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 153 280 (Polychromatic418967fa.accept_16_12_9_8_1_2508 124 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 123 153 280 (Polychromatic418967fa.accept_18_15_9_10_1_1082 123 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 153 280 (accept_3_3 122 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  121 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 153 280
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 120 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 153 280 (accept_3_3 119 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 153 280 (Polychromatic418967fa.accept_15_13_3_10_1_2296 118 153 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 153 280
  (Polychromatic418967fa.accept_21_12_6_7_1_3739 117 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 153 280 (accept_3_3 116 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 153 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 153 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 114
  153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 153 280 (accept_3_3 113
  153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 153 280
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 112 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 153 280 (Polychromatic418967fa.accept_15_6_3_10_1_2341 111 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 153 280 (accept_3_3 110 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 153 280
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 108 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 153 280 (accept_3_3 107 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 153 280 (Polychromatic418967fa.accept_21_1_6_7_1_17183 106 153 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 153 280
  (Polychromatic418967fa.accept_11_6_10_5_1_341 105 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 153 280 (accept_3_3 104 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 153 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 102 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 153 280 (accept_3_3 101 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 153 280 (Polychromatic418967fa.accept_16_4_9_8_1_2509 100 153
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 153 280
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 99 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 153 280 (accept_3_3 98 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 153 280 (Polychromatic418967fa.accept_15_6_3_10_1_2341 96 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 153 280 (accept_3_3 95 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 153 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 94 153
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 153 280
  (Polychromatic418967fa.accept_19_17_1_14_1_6360 93 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 153 280 (accept_3_3 92 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 153 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 153 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 90 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 153 280 (accept_3_3 89 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 153 280
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 88 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 153 280 (Polychromatic418967fa.accept_16_7_9_8_1_829 87 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 153 280 (accept_3_3 86 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 153 280
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 84 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 153 280 (accept_3_3 83 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 153 280 (Polychromatic418967fa.accept_13_4_10_7_1_1701 82 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 153 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 81 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 153 280 (accept_3_3 80 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 153 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 78 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 153 280 (accept_3_3 77 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 153 280 (Polychromatic418967fa.accept_16_12_9_8_1_2508 76 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 153 280 (Polychromatic418967fa.accept_19_18_1_14_1_4978 75 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 280 (accept_3_3 74 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 153 280
  (Polychromatic418967fa.accept_11_6_10_5_1_341 72 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 153 280 (accept_3_3 71 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 153 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 70 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 153 280 (Polychromatic418967fa.accept_13_4_10_7_1_1701 69 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 280 (accept_3_3 68 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 153 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 66 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 153 280 (accept_3_3 65 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 153 280 (Polychromatic418967fa.accept_13_12_10_7_1_2433 64 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 153 280 (Polychromatic418967fa.accept_16_15_9_8_1_2440 63 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 280 (accept_3_3 62 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 153 280
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 60 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 153 280 (accept_3_3 59 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 153 280 (Polychromatic418967fa.accept_15_13_3_10_1_2296 58 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 153 280 (Polychromatic418967fa.accept_23_11_15_4_1_13961 57 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 280 (accept_3_3 56 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 153 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 153 280 (accept_3_3 53 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 153 280 (Polychromatic418967fa.accept_15_7_3_10_1_817 52 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 153 280 (Polychromatic418967fa.accept_13_12_10_7_1_2433 51 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 280 (accept_3_3 50 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 280
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 153 280 (accept_3_3 47 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 153 280 (Polychromatic418967fa.accept_21_4_6_7_1_3693 46 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 153 280 (Polychromatic418967fa.accept_21_3_6_7_1_6750 45 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 280 (accept_3_3 44 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 153 280 (accept_3_3 41 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 153 280 (Polychromatic418967fa.accept_19_2_1_14_1_3663 40 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 153 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 280 (accept_3_3 38 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 280
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 153 280 (accept_3_3 35 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 153 280 (Polychromatic418967fa.accept_13_8_10_7_1_1702 34 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 153 280 (Polychromatic418967fa.accept_16_1_9_8_1_2438 33 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 280 (accept_3_3 32 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 153 280 (accept_3_3 29 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 153 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 153 280 (Polychromatic418967fa.accept_22_5_21_16_1_17204 27 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 280 (accept_3_3 26 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 280
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 153 280 (accept_3_3 23 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 153 280 (Polychromatic418967fa.accept_15_7_3_10_1_817 22 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 153 280 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 280 (accept_3_3 20 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 153 280 (accept_3_3 17 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 153 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 16 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 153 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 280 (accept_3_3 14 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 280
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 280 (accept_3_3 11 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 280 (Polychromatic418967fa.accept_19_10_1_14_1_9224 10 153 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312
  9 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 280 (accept_3_3 8
  153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 153 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 153 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 280 (accept_3_3 5 153 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 153 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 153 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 280
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 280 (accept_3_3 2 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 129 152 280 (Eq.refl Bool.true) (allA_of_3_1 129 152 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 130 151 280 (Eq.refl Bool.true) (allA_succ_of_accept 129 151 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 129 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 151 280 (accept_3_3 128 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 151 280 (Polychromatic418967fa.accept_13_10_8_7_1_1074 127 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 126 151 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 126 151 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 151 280 (accept_3_3 125 151 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 151 280 (Polychromatic418967fa.accept_11_3_8_5_1_336
  124 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 151 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 123 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 151 280 (accept_3_3 122 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 121 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 151 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 120 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 151 280 (accept_3_3 119 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 151 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 118 151
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 151 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 151 280 (accept_3_3 116 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 151 280 (Polychromatic418967fa.accept_17_13_15_8_1_3860 115 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 151 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 114 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 151 280 (accept_3_3 113 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 112 151
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 151 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 151 280 (accept_3_3 110 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 151 280 (Polychromatic418967fa.accept_22_21_19_16_1_6199 109 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 151 280 (Polychromatic418967fa.accept_16_12_7_8_1_1589 108 151 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 151 280 (accept_3_3 107 151 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 151 280
  (Polychromatic418967fa.accept_12_10_7_4_1_820 106 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 105 151 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 151 280 (accept_3_3 104 151 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 103 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 151 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 102 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 151 280 (accept_3_3 101 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 151 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 100 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 151 280 (accept_3_3 98 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 151 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 97 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 151 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 96 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 151 280 (accept_3_3 95 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 94 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 151 280 (accept_3_3 92 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 151 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 91 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 151 280
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 90 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 151 280 (accept_3_3 89 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 151 280 (Polychromatic418967fa.accept_13_10_8_7_1_1074 88 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 151 280 (accept_3_3 86 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 151 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 84 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 151 280 (accept_3_3 83 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 151 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 82 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 151 280 (accept_3_3 80 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 151 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 79 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 151 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 151 280 (accept_3_3 77 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 151 280 (accept_3_3 74 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 151 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 73 151 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 151 280
  (Polychromatic418967fa.accept_19_15_18_14_1_3564 72 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 151 280 (accept_3_3 71 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 151 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 151 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 151 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 151 280 (accept_3_3 68 151 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379
  67 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 151 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 151 280 (accept_3_3 65 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 151 280 (Polychromatic418967fa.accept_13_12_8_7_1_2526 64 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 151 280 (accept_3_3 62 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 151 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 61 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 151 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 151 280 (accept_3_3 59 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 151 280 (accept_3_3 56 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 151 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135 55 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 280
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 54 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 151 280 (accept_3_3 53 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 151 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 52 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 280 (accept_3_3 50 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 151 280 (accept_3_3 47 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 151 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 46 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 280 (accept_3_3 44 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 43 151 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 151 280 (accept_3_3 41 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 280 (accept_3_3 38 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 36 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 151 280 (accept_3_3 35 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 151 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 280 (accept_3_3 32 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 280 (accept_3_3 29 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 280 (Polychromatic418967fa.accept_13_2_8_7_1_2424 28 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 280 (accept_3_3 26 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 25 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 280 (accept_3_3 23 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 280 (accept_3_3 20 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 280 (Polychromatic418967fa.accept_21_19_4_7_1_3775 19 151 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 280
  (Polychromatic418967fa.accept_21_18_4_7_1_8346 18 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 280 (accept_3_3 17 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 280 (accept_3_3 14 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 280 (accept_3_3 11 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 280 (accept_3_3 8 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 280 (accept_3_3 5 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 151 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 280 (accept_3_3 2 151 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 280 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 151 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 131 150 280 (Eq.refl Bool.true) (allA_succ_of_gcd 130 150 280 10 13 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 150 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 129 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 150 280 2 64 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 150 280 (Polychromatic418967fa.accept_21_1_3_7_1_3727 127 150 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 150 280 2 63 75 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 125 150 280 5 25 30 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 124 150 280 2 62 75 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 150 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 123 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 150 280 2 61 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 150 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 121 150 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 150 280 10 12 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 150 280 (accept_3_3 119 150 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 150 280 2 59 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 150 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 117 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 150 280 2 58 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 115 150 280 5 23 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 114 150 280 2 57 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 150 280 (accept_3_3 113 150 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 112 150 280 2 56 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 111 150 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 111 150 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 150 280 10 11 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 150 280
  (Polychromatic418967fa.accept_17_7_14_8_1_5069 109 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 150 280 2 54 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 150 280 (accept_3_3 107 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 150 280 2 53 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 150 280 5 21 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 150 280 2 52 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 150 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 103 150
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 150 280 2 51 75 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 150 280 (accept_3_3
  101 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 150 280 10 10 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 150 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 99 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 150 280 2 49 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 150 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 97 150 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 150 280 2 48 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 150 280 5 19 30 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 150 280 2 47 75 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 150 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 93 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 150 280 2 46 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 150 280 (Polychromatic418967fa.accept_17_6_14_8_1_3858 91 150 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 150 280 10 9 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 150 280 (accept_3_3 89 150 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 150 280 2 44 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 150 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 87 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 150 280 2 43 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 150 280 5 17 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 150 280 2 42 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 150 280 (accept_3_3 83 150 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 150 280 2 41 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 150 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 150 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 150 280 10 8 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 150 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 79 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 280 2 39 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 280 (accept_3_3 77 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 150 280 2 38 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 150 280 5 15 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 150 280 2 37 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 280 (Polychromatic418967fa.accept_19_16_17_14_1_4969 73 150
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 150 280 2 36 75 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 150 280 (accept_3_3 71
  150 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 150 280 10 7 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 150 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 69 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 150 280 2 34 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 150 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 150 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 150 280 2 33 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 150 280 5 13 30 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 150 280 2 32 75 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 150 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 63 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 150 280 2 31 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 150 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 150 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 150 280 10 6 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 150 280 (accept_3_3 59 150 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 280 2 29 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 150 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57
  150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 150 280 2 28 75 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 150 280 5 11 30 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 150 280 2 27 75
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 150 280
  (accept_3_3 53 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 280 2 26 75 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 51 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 280 10 5 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 150 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 150 280 2 24 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 150 280 (accept_3_3 47 150 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 280 2 23 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 150 280 5 9 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 280 2 22 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 280 2 21 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 280 (accept_3_3 41 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 280 10 4 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 150 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 150 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 150 280 2 19 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 280
  (Polychromatic418967fa.accept_21_16_3_7_1_6705 37 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 280 2 18 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 150 280 5 7 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 150 280 2 17 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 150 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 150 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 150 280 2 16 75 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 280 10 3 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 280 (accept_3_3 29 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 280 2 14 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 150 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 150 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 150 280 2 13 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 150 280 5 5 30 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 150 280 2 12 75 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 280 (accept_3_3 23 150 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 280 2 11 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 280 10 2 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 280 (Polychromatic418967fa.accept_27_19_15_10_1_11622 19 150 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 280 2 9 75 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 280 (accept_3_3 17 150 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 280 2 8 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 280 5 3 30 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 280 2 7 75 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 280 2 6 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 280 (accept_3_3 11 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 280 10 1 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 150 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 150 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 280 2 4 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 280 2 3 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 150 280 5 1 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 150 280 2 2 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 150 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 150 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 280 2 1 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 280 (Polychromatic418967fa.accept_19_1_17_14_1_7882
  1 150 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 132 149 280 (Eq.refl Bool.true) (allA_of_3_1 132 149 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 133 148 280 (Eq.refl Bool.true) (allA_succ_of_gcd 132 148 280 4 33 37 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 148 280 (accept_3_3 131 148 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 148 280 2 65 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 148 280 (Polychromatic418967fa.accept_9_3_4_1_1_22
  129 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 148 280 4 32 37 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 148 280
  (Polychromatic418967fa.accept_16_15_4_8_1_1562 127 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 148 280 2 63 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 148 280 (accept_3_3 125 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 148 280 4 31 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 148 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 123 148 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 148 280 2 61 74 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 148 280
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 121 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 120 148 280 4 30 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 119 148 280 (accept_3_3 119 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 148 280 2 59 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 148 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 117 148 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 148 280 4 29 37 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 148 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 115 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 148 280 2 57 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 148 280 (accept_3_3 113 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 148 280 4 28 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 148 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 111 148 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 148 280 2 55 74 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 148 280
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 109 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 148 280 4 27 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 148 280 (accept_3_3 107 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 148 280 2 53 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 148 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 105 148 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 148 280 4 26 37 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 148 280
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 103 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 148 280 2 51 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 148 280 (accept_3_3 101 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 148 280 4 25 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 148 280 (Polychromatic418967fa.accept_16_3_4_8_1_3450 99 148 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 148 280 2 49 74 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 148 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 97 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 148 280 4 24 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 148 280 (accept_3_3 95 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 148 280 2 47 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 148 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 93 148 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 148 280 4 23 37 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 148 280
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 91 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 148 280 2 45 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 148 280 (accept_3_3 89 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 148 280 4 22 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 148 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 87 148 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 148 280 2 43 74 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 148 280
  (Polychromatic418967fa.accept_16_5_4_8_1_1560 85 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 148 280 4 21 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 148 280 (accept_3_3 83 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 148 280 2 41 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 148 280 (Polychromatic418967fa.accept_16_1_4_8_1_3434 81 148 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 148 280 4 20 37 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 148 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 79 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 148 280 2 39 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 148 280 (accept_3_3 77 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 148 280 4 19 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 148 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 75 148 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 148 280 2 37 74 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 148 280
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 73 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 148 280 4 18 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 148 280 (accept_3_3 71 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 280 2 35 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 148 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 280 4 17 37 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 280
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 67 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 148 280 2 33 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 148 280 (accept_3_3 65 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 280 4 16 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 280 (Polychromatic418967fa.accept_13_11_5_7_1_2420 63 148 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 280 2 31 74 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 61 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 280 4 15 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 280 (accept_3_3 59 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 280 2 29 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 148 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 280 4 14 37 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 280
  (Polychromatic418967fa.accept_16_7_4_8_1_2487 55 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 148 280 2 27 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 148 280 (accept_3_3 53 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 280 4 13 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 148 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 280 2 25 74 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 280
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 148 280 4 12 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 148 280 (accept_3_3 47 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 280 2 23 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 280 (Polychromatic418967fa.accept_16_13_4_8_1_4557 45 148 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 280 4 11 37 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 280 2 21 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 280 (accept_3_3 41 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 280 4 10 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 148 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 280 2 19 74 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 280
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 37 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 280 4 9 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 148 280 (accept_3_3 35 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  148 280 2 17 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 148 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 148 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 280 4 8 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 280
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 148 280 2 15 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 148 280 (accept_3_3 29 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 280 4 7 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 148 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 27 148 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 280 2 13 74 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 280 4 6 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 148 280 (accept_3_3 23 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  148 280 2 11 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 148 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 148 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 280 4 5 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 280
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 148 280 2 9 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 148 280 (accept_3_3 17 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 148 280 4 4 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 148 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 148 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 280 2 7 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 280 (Polychromatic418967fa.accept_16_13_4_8_1_4557
  13 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 280 4 3 37 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 280
  (accept_3_3 11 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 280 2 5 74 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 280
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 280 4 2 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 148 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 280 2 3 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 280 (accept_3_3 5 148 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148 280 4 1 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 148 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 148 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 280 2 1 74 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 280
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 148 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 148
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 134 147 280 (Eq.refl Bool.true) (allA_succ_of_gcd 133 147 280 7 19 21 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 132 147 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 132 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 147 280 (accept_3_3 131 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  130 147 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 130 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 147 280 (Polychromatic418967fa.accept_13_12_4_7_1_2520 129 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 147 280 (accept_3_3 128 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 127 147 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 147 280 7 18 21 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 147 280 (accept_3_3
  125 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 147 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 124 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 147 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 123 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 147 280 (accept_3_3 122 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 121 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 121 147 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 147 280
  (Polychromatic418967fa.accept_11_10_4_5_1_359 120 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 119 147 280 7 17 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 118 147 280 (Polychromatic418967fa.accept_15_13_12_10_1_4352 118 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 147 280
  (Polychromatic418967fa.accept_16_5_3_8_1_4555 117 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 147 280 (accept_3_3 116 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 147 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 114 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 147 280 (accept_3_3 113 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 147 280 7 16 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 147 280
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 111 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 147 280 (accept_3_3 110 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 147 280 (Polychromatic418967fa.accept_16_12_3_8_1_5729 108
  147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 147 280 (accept_3_3 107
  147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 147 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 106 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 147 280 7 15 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 147 280 (accept_3_3 104 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 147 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 102 147
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 147 280 (accept_3_3 101 147
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 147 280
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 100 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 147 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 99 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 147 280 7 14 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97
  147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 147 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 96 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 147 280 (accept_3_3 95 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 147 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 94 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 147 280 (Polychromatic418967fa.accept_16_13_3_8_1_2422 93 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 147 280 (accept_3_3 92 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 147 280 7 13 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 147 280 (Polychromatic418967fa.accept_12_6_3_4_1_394
  90 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 147 280 (accept_3_3 89
  147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 88 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 147 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 147 280 (accept_3_3 86 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 147 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 147 280 7 12 21 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 147 280 (accept_3_3 83 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 280 (Polychromatic418967fa.accept_15_7_12_10_1_4335 82 147
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 147 280
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 81 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 147 280 (accept_3_3 80 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 147 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 78 147 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 147 280 7 11 21 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 147 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 76 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 147 280 (Polychromatic418967fa.accept_13_10_4_7_1_2465 75 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 147 280 (accept_3_3 74 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 147 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 280
  (Polychromatic418967fa.accept_29_14_2_19_1_17203 72 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 147 280 (accept_3_3 71 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 147 280 7 10 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 147 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 147 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 147 280 (accept_3_3 68 147 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 147 280 (accept_3_3 65 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 147 280 (Polychromatic418967fa.accept_13_12_4_7_1_2520 64 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 147 280 7 9 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 147 280 (accept_3_3 62 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 147 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 280 (accept_3_3 59 147 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 280 (Polychromatic418967fa.accept_9_4_3_1_1_154
  58 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 280
  (Polychromatic418967fa.accept_24_9_3_16_1_17175 57 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 147 280 7 8 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 280
  (Polychromatic418967fa.accept_11_10_4_5_1_359 54 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 147 280 (accept_3_3 53 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 147 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 147 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 147 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 280 (accept_3_3 50 147 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 49 147 280 7 7 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 147 280 (Polychromatic418967fa.accept_13_9_4_7_1_1694 48 147
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 280 (accept_3_3 47 147
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 280
  (Polychromatic418967fa.accept_27_19_12_10_1_11620 46 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 147 280 (Polychromatic418967fa.accept_13_6_4_7_1_2464 45 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 280 (accept_3_3 44 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 147 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 147 280 7 6 21 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 147 280 (accept_3_3 41
  147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 40 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 147 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 39 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 280 (accept_3_3 38 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 147 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 280
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 147 280 7 5 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 147 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 147 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 280 (accept_3_3 32 147 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 147 280 (accept_3_3 29 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28
  147 280 7 4 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 147 280 (Polychromatic418967fa.accept_16_11_3_8_1_4597 27 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 280 (accept_3_3 26 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 147 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 280 (accept_3_3 23 147 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 280 (Polychromatic418967fa.accept_9_4_3_1_1_154
  22 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 280 7 3 21 40
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 280
  (accept_3_3 20 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 147 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 280 (accept_3_3 17 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 147 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 147 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 280 (Polychromatic418967fa.accept_9_6_3_1_1_155
  15 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 147 280 7 2 21 40
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 147 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 147 280 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 280 (accept_3_3 11 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 147 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 147 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 280
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 280 (accept_3_3 8 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 147
  280 7 1 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  147 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 147 280 (accept_3_3 5 147 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 147 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 280 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 147 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 280 (accept_3_3 2 147 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  147 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 135 146 280 (Eq.refl Bool.true) (allA_of_3_1 135 146 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 136 145 280 (Eq.refl Bool.true) (allA_succ_of_gcd 135 145 280 5 27 29 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 134 145 280 (accept_3_3 134 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 145 280 (Polychromatic418967fa.accept_25_8_20_5_1_17202 133
  145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 145 280
  (Polychromatic418967fa.accept_16_4_1_8_1_835 132 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 145 280 (accept_3_3 131 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  130 145 280 5 26 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 129 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 129 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 145 280 (accept_3_3 128 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 127 145 280 (Polychromatic418967fa.accept_16_15_1_8_1_1585 127 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 145 280
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 126 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 125 145 280 5 25 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 124 145 280 (Polychromatic418967fa.accept_16_12_1_8_1_5767 124 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 145 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 123 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 145 280 (accept_3_3 122 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 145 280 (Polychromatic418967fa.accept_16_9_1_8_1_5766 121 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 120 145 280 5 24 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 119 145 280 (accept_3_3 119 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 145 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 118 145 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25
  117 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 145 280 (accept_3_3
  116 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 115 145 280 5 23 29 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 114 145 280
  (Polychromatic418967fa.accept_21_9_19_7_1_8376 114 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 145 280 (accept_3_3 113 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 145 280 (Polychromatic418967fa.accept_13_8_2_7_1_2452 112 145 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25
  111 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 145 280 5 22 29 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 145 280
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 109 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 145 280 (Polychromatic418967fa.accept_16_12_1_8_1_5767 108 145 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 145 280 (accept_3_3 107 145 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 145 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 106 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 145 280 5 21 29 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 145 280 (accept_3_3
  104 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 145 280
  (Polychromatic418967fa.accept_16_7_1_8_1_5796 103 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 145 280 (Polychromatic418967fa.accept_19_7_12_14_1_9206 102 145 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 145 280 (accept_3_3 101 145 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 100 145 280 5 20 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 145 280 (accept_3_3 98 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 145 280
  (Polychromatic418967fa.accept_19_2_12_14_1_11919 97 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 145 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 96 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 145 280 5 19 29 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 145 280
  (Polychromatic418967fa.accept_12_10_1_4_1_392 94 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 145 280 (accept_3_3 92 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 145 280 (Polychromatic418967fa.accept_17_6_9_8_1_6316 91 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 145 280 5 18 29 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 145 280 (accept_3_3 89 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 145 280
  (Polychromatic418967fa.accept_18_16_1_10_1_2029 88 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 145 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 145 280 (accept_3_3 86 145 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 85 145 280 5 17 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 145 280 (Polychromatic418967fa.accept_16_4_1_8_1_835 84 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 145 280 (accept_3_3 83 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 145 280 (Polychromatic418967fa.accept_12_10_1_4_1_392
  82 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 145 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 145 280 5 16 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 145 280 (Polychromatic418967fa.accept_16_15_1_8_1_1585 79 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 145 280
  (Polychromatic418967fa.accept_19_2_12_14_1_11919 78 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 145 280 (accept_3_3 77 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 145 280 (Polychromatic418967fa.accept_16_12_1_8_1_5767 76 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 145 280 5 15 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 145 280 (accept_3_3 74 145 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 145 280 (Polychromatic418967fa.accept_13_8_2_7_1_2452 73 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 280
  (Polychromatic418967fa.accept_21_9_19_7_1_8376 72 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 145 280 (accept_3_3 71 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  145 280 5 14 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 145 280 (accept_3_3 68 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 145 280 (Polychromatic418967fa.accept_17_16_9_8_1_5063 67 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 145 280
  (Polychromatic418967fa.accept_19_9_12_14_1_4966 66 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 145 280 5 13 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 145 280 (Polychromatic418967fa.accept_19_7_12_14_1_9206 64 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 145 280 (accept_3_3 62 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 145 280 (Polychromatic418967fa.accept_13_9_2_7_1_1083 61 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 145 280 5 12 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 145 280 (accept_3_3 59 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 145 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 145 280 (accept_3_3 56 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 145 280 5 11 29 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 145 280
  (Polychromatic418967fa.accept_19_16_12_14_1_10640 54 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 145 280 (accept_3_3 53 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 145 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 52 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 145 280 5 10 29 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 145 280
  (Polychromatic418967fa.accept_18_13_1_10_1_4331 49 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 280 (Polychromatic418967fa.accept_13_9_2_7_1_1083 48 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 280 (accept_3_3 47 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 145
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 145 280 5 9 29 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 145 280 (accept_3_3 44
  145 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 280
  (Polychromatic418967fa.accept_21_1_19_7_1_1218 43 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 145 280 (Polychromatic418967fa.accept_25_17_20_5_1_10279 42 145 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 280 (accept_3_3 41 145 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 145 280 5 8 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 280 (accept_3_3 38 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 280
  (Polychromatic418967fa.accept_23_14_7_4_1_14071 37 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 280 (Polychromatic418967fa.accept_16_4_1_8_1_835 36 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 145 280 5 7 29 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 145 280
  (Polychromatic418967fa.accept_12_10_1_4_1_392 34 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 280 (accept_3_3 32 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 145 280 (Polychromatic418967fa.accept_13_5_2_7_1_2414 31 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 145 280 5 6 29 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 145 280 (accept_3_3 29 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 280
  (Polychromatic418967fa.accept_16_12_1_8_1_5767 28 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 280 (accept_3_3 26 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 145 280 5 5 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 145 280 (Polychromatic418967fa.accept_22_2_13_16_1_6117 24 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 280 (accept_3_3 23 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 280 (Polychromatic418967fa.accept_12_10_1_4_1_392
  22 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 145 280 5 4 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 145 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 280 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 145
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 280 (accept_3_3 17 145
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 280
  (Polychromatic418967fa.accept_17_16_9_8_1_5063 16 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 145 280 5 3 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 145 280 (accept_3_3 14 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 280 (Polychromatic418967fa.accept_18_13_1_10_1_4331 13 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 280 (Polychromatic418967fa.accept_16_12_1_8_1_5767 12 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 280 (accept_3_3 11 145 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 145 280 5 2 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 145 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9
  145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 280 (accept_3_3 8 145
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 280
  (Polychromatic418967fa.accept_16_7_1_8_1_5796 7 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 145 280 (Polychromatic418967fa.accept_17_6_9_8_1_6316 6 145 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 145 280 5 1 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 145 280 (Polychromatic418967fa.accept_16_4_1_8_1_835 4 145 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 280 (accept_3_3 2 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 280 (Polychromatic418967fa.accept_17_1_9_8_1_7492 1 145 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 137 144 280 (Eq.refl Bool.true) (allA_succ_of_gcd 136 144 280 8 17 18 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 135 144 280
  (Polychromatic418967fa.accept_21_9_18_7_1_5180 135 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 134 144 280 2 67 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 133 144 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 133 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 144 280 4 33 36 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 144 280 (accept_3_3
  131 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 144 280 2 65 72 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 144 280
  (Polychromatic418967fa.accept_19_15_11_14_1_11940 129 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 128 144 280 8 16 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 127 144 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 127 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 144 280 2 63 72 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 144 280 (accept_3_3
  125 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 144 280 4 31 36 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 144 280
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 123 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 144 280 2 61 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 144 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 121 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 144 280 8 15 18 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 144 280 (accept_3_3 119 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 144 280 2 59 72 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 144 280
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 117 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 144 280 4 29 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 144 280 (Polychromatic418967fa.accept_13_11_1_7_1_1691 115 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 144 280 2 57 72 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 144 280 (accept_3_3
  113 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 144 280 8 14 18 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 144 280
  (Polychromatic418967fa.accept_19_16_11_14_1_3608 111 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 144 280 2 55 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 144 280 (Polychromatic418967fa.accept_15_4_9_10_1_5384 109 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 144 280 4 27 36 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 144 280 (accept_3_3
  107 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 144 280 2 53 72 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 144 280
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 105 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 144 280 8 13 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 144 280 (Polychromatic418967fa.accept_21_19_18_7_1_8388 103 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 144 280 2 51 72 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 144 280 (accept_3_3 101 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 144 280 4 25 36 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 144 280
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 99 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 144 280 2 49 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 144 280 (Polychromatic418967fa.accept_13_6_1_7_1_1690 97 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 144 280 8 12 18 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 144 280 (accept_3_3 95 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 144 280 2 47 72 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 144 280
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 93 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 144 280 4 23 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 144 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 91 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 144 280 2 45 72 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 144 280 (accept_3_3 89 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 144 280 8 11 18 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 144 280
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 87 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 144 280 2 43 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 144 280 (Polychromatic418967fa.accept_19_9_11_14_1_10626 85 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 144 280 4 21 36 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 144 280 (accept_3_3 83
  144 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 144 280 2 41 72 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 144 280
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 81 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 144 280 8 10 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 144 280 (Polychromatic418967fa.accept_15_4_9_10_1_5384 79 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 144 280 2 39 72 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 144 280 (accept_3_3 77 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 144 280 4 19 36 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 144 280
  (Polychromatic418967fa.accept_21_12_18_7_1_6740 75 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 144 280 2 37 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 144 280 (Polychromatic418967fa.accept_13_8_1_7_1_2505 73 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 144 280 8 9 18 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 144 280 (accept_3_3 71 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 144 280 2 35 72 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 144 280
  (Polychromatic418967fa.accept_21_6_18_7_1_3764 69 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 144 280 4 17 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 144 280 (Polychromatic418967fa.accept_21_4_18_7_1_5211 67 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 144 280 2 33 72 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 144 280 (accept_3_3 65 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 280 8 8 18 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 144 280
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 144 280 2 31 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 144 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 61 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 144 280 4 15 36 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 144 280 (accept_3_3 59 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 280 2 29 72 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 280
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 57 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 144 280 8 7 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 144 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 55 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 144 280 2 27 72 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 144 280 (accept_3_3 53 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 280 4 13 36 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 280
  (Polychromatic418967fa.accept_21_9_18_7_1_5180 51 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 144 280 2 25 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 144 280 (Polychromatic418967fa.accept_15_4_9_10_1_5384 49 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 144 280 8 6 18 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 144 280 (accept_3_3 47 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 280 2 23 72 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 144 280
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 144 280 4 11 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 144 280 (Polychromatic418967fa.accept_19_5_11_14_1_3654 43 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 144 280 2 21 72 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 144 280 (accept_3_3 41 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 280 8 5 18 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 280
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 144 280 2 19 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 144 280 (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 280 4 9 36 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 280 (accept_3_3 35 144 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 280 2 17 72 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 280
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 144 280 8 4 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 144 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 31 144 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 280 2 15 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 280 (accept_3_3 29 144 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 280 4 7 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 280 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 144
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 280 2 13 72 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 280
  (Polychromatic418967fa.accept_19_6_11_14_1_10624 25 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 144 280 8 3 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 144 280 (accept_3_3 23 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 144 280 2 11 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 144 280 (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 280 4 5 36 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 280
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 280 2 9 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 144 280 (accept_3_3 17 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 280 8 2 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 144 280 (Polychromatic418967fa.accept_19_15_11_14_1_11940 15 144 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 280 2 7 72 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 280
  (Polychromatic418967fa.accept_21_13_18_7_1_1216 13 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 144 280 4 3 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 144 280 (accept_3_3 11 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 280 2 5 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 144 280 (Polychromatic418967fa.accept_19_9_11_14_1_10626 9 144 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 280 8 1 18 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 280
  (Polychromatic418967fa.accept_19_7_11_14_1_11901 7 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 144 280 2 3 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 144 280 (accept_3_3 5 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 144 280 4 1 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 144 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3 144 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 280 2 1 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327
  1 144 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 138 143 280 (Eq.refl Bool.true) (allA_of_3_1 138 143 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 139 142 280 (Eq.refl Bool.true) (allA_succ_of_gcd 138 142 280 2 69 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 137 142 280 (accept_3_3 137 142 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 136 142 280 2 68 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 135 142 280
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 135 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 134 142 280 2 67 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 133 142 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 133 142 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 142 280 2 66 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 142 280 (accept_3_3
  131 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 142 280 2 65 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 142 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 129 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 142 280 2 64 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 142 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 127 142 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 142 280 2 63 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 142 280 (accept_3_3 125 142 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 142 280 2 62 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 142 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 123 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 142 280 2 61 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 142 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 121 142 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 142 280 2 60 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 142 280 (accept_3_3 119 142 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 142 280 2 59 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 142 280
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 117 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 142 280 2 58 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 142 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 115 142 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 142 280 2 57 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 142 280 (accept_3_3
  113 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 142 280 2 56 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 142 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 111 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 142 280 2 55 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 142 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 109 142 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 142 280 2 54 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 142 280 (accept_3_3 107 142 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 142 280 2 53 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 142 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 105 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 142 280 2 52 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 142 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 103 142 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 142 280 2 51 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 142 280 (accept_3_3 101 142 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 142 280 2 50 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 142 280
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 99 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 142 280 2 49 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 142 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 97 142 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 142 280 2 48 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 142 280 (accept_3_3 95 142 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 142 280 2 47 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 142 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 93 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 142 280 2 46 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 142 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 91 142 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 142 280 2 45 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 142 280 (accept_3_3 89 142 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 142 280 2 44 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 142 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 87 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 142 280 2 43 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 142 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 142 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 142 280 2 42 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 142 280 (accept_3_3 83 142 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 142 280 2 41 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 142 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202
  81 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 142 280 2 40 71 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 142 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 79 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 142 280 2 39 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 142 280 (accept_3_3 77 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 142 280 2 38 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 142 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 142 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 142 280 2 37 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 142 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 142 280 2 36 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 142 280 (accept_3_3 71 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 142 280 2 35 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 142 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 142 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 280 2 34 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 67 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 280 2 33 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 280 (accept_3_3 65 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 280 2 32 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 280 (Polychromatic418967fa.accept_13_11_12_7_1_2443 63 142 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 280 2 31 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 280
  (Polychromatic418967fa.accept_11_6_10_5_1_341 61 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 142 280 2 30 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 142 280 (accept_3_3 59 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 280 2 29 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 142 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 280 2 28 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 280 2 27 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 280 (accept_3_3 53 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 280 2 26 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 142 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 280 2 25 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 280 2 24 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 280 (accept_3_3 47 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 280 2 23 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 280 (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 142 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 280 2 22 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 280 2 21 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 280 (accept_3_3 41 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 280 2 20 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 142 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 280 2 19 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 280
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 280 2 18 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 280 (accept_3_3 35 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 280 2 17 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 142 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 280 2 16 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 280 2 15 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 280 (accept_3_3 29 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 280 2 14 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 280 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 142 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 280 2 13 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 280 2 12 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 280 (accept_3_3 23 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 280 2 11 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 142 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 280 2 10 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 280 2 9 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 280 (accept_3_3 17 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 280 2 8 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 142 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 280 2 7 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 280 2 6 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 280 (accept_3_3 11 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 280 2 5 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 280 (Polychromatic418967fa.accept_17_9_6_8_1_6315 9 142 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 280 2 4 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 280 2 3 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 280 (accept_3_3 5 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  280 2 2 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 142 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 280 2 1 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 142 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 140 141 280 (Eq.refl Bool.true) (allA_succ_of_accept 139 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  139 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 138 141 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 138 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 137 141 280 (accept_3_3 137 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  136 141 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 136 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 135 141 280 (Polychromatic418967fa.accept_13_5_11_7_1_559 135 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 141 280 (accept_3_3 134 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 133 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 141 280
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 132 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 131 141 280 (accept_3_3 131 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 141 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 130 141 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 141 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 129 141
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 141 280 (accept_3_3 128 141
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 141 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 127 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 126 141 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 126 141 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 141 280 (accept_3_3 125 141 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 124 141 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 124 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 141 280
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 123 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 141 280 (accept_3_3 122 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 121 141 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 141 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 120 141
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 141 280 (accept_3_3 119 141
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 141 280
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 118 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 141 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 117 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 141 280 (accept_3_3 116 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 141 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 114 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 141 280 (accept_3_3 113 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 141 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 112 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 141 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 111 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 141 280 (accept_3_3 110 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 141 280
  (Polychromatic418967fa.accept_13_4_11_7_1_558 108 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 141 280 (accept_3_3 107 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 141 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 106 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 141 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 105 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 141 280 (accept_3_3 104 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 141 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 102 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 141 280 (accept_3_3 101 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 141 280 (Polychromatic418967fa.accept_13_9_11_7_1_1077 100 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 141 280 (Polychromatic418967fa.accept_16_3_13_8_1_1594 99 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 141 280 (accept_3_3 98 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97
  141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 141 280
  (Polychromatic418967fa.accept_13_5_11_7_1_559 96 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 141 280 (accept_3_3 95 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 141 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 94 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 141 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 141 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 141 280 (accept_3_3 92 141 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 90 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 141 280 (accept_3_3 89 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 141 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 88 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 141 280 (Polychromatic418967fa.accept_13_9_11_7_1_1077 87 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 141 280 (accept_3_3 86 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 141 280 (accept_3_3 83 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 141 280 (Polychromatic418967fa.accept_13_4_11_7_1_558 82 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 141 280 (Polychromatic418967fa.accept_13_3_11_7_1_2488 81 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 280 (accept_3_3 80 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 78 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 141 280 (accept_3_3 77 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 141 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 141 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 141 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 280 (accept_3_3 74 141 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 280
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 72 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 141 280 (accept_3_3 71 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 141 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 141 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 141 280 (Polychromatic418967fa.accept_13_4_11_7_1_558 69 141
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 280 (accept_3_3 68 141
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  67 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 141 280 (accept_3_3 65 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 141 280 (Polychromatic418967fa.accept_13_12_11_7_1_2491 64 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 141 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539 63 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 280 (accept_3_3 62 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 280
  (Polychromatic418967fa.accept_16_12_13_8_1_2409 60 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 141 280 (accept_3_3 59 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 141 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 280 (accept_3_3 56 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55
  141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 141 280 (accept_3_3 53 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 141 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 141 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 51 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 280 (accept_3_3 50 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 141 280 (accept_3_3 47 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 141 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 141 280 (Polychromatic418967fa.accept_18_9_15_10_1_395 45 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 280 (accept_3_3 44 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 141 280 (accept_3_3 41 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 141 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 141 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 141 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 280 (accept_3_3 38 141 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 280
  (Polychromatic418967fa.accept_16_4_13_8_1_3424 36 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 141 280 (accept_3_3 35 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 141 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 141 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 280 (accept_3_3 32 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 141 280 (accept_3_3 29 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 141 280 (Polychromatic418967fa.accept_16_12_13_8_1_2409 28 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 141 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 280 (accept_3_3 26 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 280
  (Polychromatic418967fa.accept_18_6_15_10_1_6975 24 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 280 (accept_3_3 23 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 141 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 280 (accept_3_3 20 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 280
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 280 (accept_3_3 17 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 280 (Polychromatic418967fa.accept_22_15_9_16_1_17201 15 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 280 (accept_3_3 14 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 280 (accept_3_3 11 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 280 (Polychromatic418967fa.accept_21_10_15_7_1_3784 10 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 280 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 280 (accept_3_3 8 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 141 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 280 (accept_3_3 5 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 141 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 141 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 280 (accept_3_3 2 141 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 140 280 (allA_of_3_1 140 140 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 139 280
  (allA_succ_of_accept 138 139 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 138 139 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 139 280 (accept_3_3 137 139 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 136 139 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430 136 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 135 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 134 139 280 (accept_3_3 134 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  133 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 133 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 132 139 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 132 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 139 280 (accept_3_3 131 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 139 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 130 139
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 129 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 139 280 (accept_3_3 128 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 139 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 127 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 126 139 280 (Polychromatic418967fa.accept_15_6_4_10_1_2319 126 139 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 139 280 (accept_3_3 125 139 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391
  124 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 123 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 139 280 (accept_3_3 122 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 139 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 121 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 139 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 120 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 139 280 (accept_3_3 119 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 139 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 118 139
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 139 280 (accept_3_3 116 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 115 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 139 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 114 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 139 280 (accept_3_3 113 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 139 280 (Polychromatic418967fa.accept_13_8_9_7_1_530 112 139
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 139 280 (accept_3_3 110 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 139 280 (Polychromatic418967fa.accept_16_13_11_8_1_2449 109 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 139 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 108 139 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 139 280 (accept_3_3 107 139 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391
  106 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 139 280 (accept_3_3 104 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 139 280 (Polychromatic418967fa.accept_15_13_4_10_1_821 103 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 139 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 102 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 139 280 (accept_3_3 101 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 139 280 (Polychromatic418967fa.accept_16_4_11_8_1_1574 100
  139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 139 280 (accept_3_3 98 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 97 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 139 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 96 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 139 280 (accept_3_3 95 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 139 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 94 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 139 280 (accept_3_3 92 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 139 280 (Polychromatic418967fa.accept_18_1_13_10_1_2024 91 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 139 280 (Polychromatic418967fa.accept_17_5_3_8_1_1697 90 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 139 280 (accept_3_3 89 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 139 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 139 280 (accept_3_3 86 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 139 280 (Polychromatic418967fa.accept_16_5_11_8_1_3431 85 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 139 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 139 280 (accept_3_3 83 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 139 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 82 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 139 280 (accept_3_3 80 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 139 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 78 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 139 280 (accept_3_3 77 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 139 280 (Polychromatic418967fa.accept_13_11_9_7_1_2484 76 139 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 139 280 (accept_3_3 74 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 139 280 (Polychromatic418967fa.accept_13_8_9_7_1_530 73 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 139 280 (Polychromatic418967fa.accept_21_9_13_7_1_5154 72 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 280 (accept_3_3 71 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 139 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 139 280 (accept_3_3 68 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 139 280 (Polychromatic418967fa.accept_13_2_9_7_1_164 67 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 139 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 280 (accept_3_3 65 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 64 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 139 280 (accept_3_3 62 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 139 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 280 (accept_3_3 59 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 280 (accept_3_3 56 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 55 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 280 (Polychromatic418967fa.accept_13_2_9_7_1_164 54 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 280 (accept_3_3 53 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 139 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 280 (accept_3_3 50 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 280 (Polychromatic418967fa.accept_19_11_6_14_1_6362 49 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 280 (accept_3_3 47 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 280 (accept_3_3 44 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 280 (accept_3_3 41 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 280 (Polychromatic418967fa.accept_18_4_13_10_1_2064 40 139 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 280 (accept_3_3 38 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 280 (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 280 (Polychromatic418967fa.accept_15_6_4_10_1_2319 36 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 280 (accept_3_3 35 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 139 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 280 (accept_3_3 32 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 280 (accept_3_3 29 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 280 (Polychromatic418967fa.accept_13_2_9_7_1_164 28 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 280 (accept_3_3 26 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 280 (accept_3_3 23 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 280 (accept_3_3 20 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 280 (Polychromatic418967fa.accept_21_18_13_7_1_9883 18 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 280 (accept_3_3 17 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 139 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 280 (accept_3_3 14 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 280 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 280 (accept_3_3 11 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 280 (accept_3_3 8 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 280 (accept_3_3 5 139 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 139 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 280 (accept_3_3 2 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 280 (Polychromatic418967fa.accept_18_1_13_10_1_2024 1 139 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 138 280 (allA_succ_of_accept 137 138 280 (accept_3_3 137 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 136 138 280 2 68 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 135 138 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 135 138 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 134 138 280 2 67 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 138 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 133 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 138 280 2 66 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 138 280 (accept_3_3 131 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 138 280 2 65 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 138 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 129 138 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 138 280 2 64 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 138 280
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 127 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 138 280 2 63 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 138 280 (accept_3_3 125 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 138 280 2 62 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 138 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 123 138 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 138 280 2 61 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 138 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 121 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 138 280 2 60 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 138 280 (accept_3_3 119 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 138 280 2 59 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 138 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 117 138 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 138 280 2 58 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 138 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 115 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 138 280 2 57 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 138 280 (accept_3_3 113 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 138 280 2 56 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 138 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 111 138 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 138 280 2 55 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 138 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 109 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 138 280 2 54 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 138 280 (accept_3_3 107 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 138 280 2 53 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 138 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 105 138 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 138 280 2 52 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 138 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 103 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 138 280 2 51 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 138 280 (accept_3_3 101 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 138 280 2 50 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 138 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 99 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 138 280 2 49 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 138 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 97 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 138 280 2 48 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 138 280 (accept_3_3 95 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 138 280 2 47 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 138 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 93 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 138 280 2 46 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 138 280
  (Polychromatic418967fa.accept_24_19_18_16_1_5216 91 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 138 280 2 45 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 138 280 (accept_3_3 89 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 138 280 2 44 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 138 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 138 280 2 43 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 138 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 85 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 280 2 42 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 280 (accept_3_3 83 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 138 280 2 41 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 138 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 138 280 2 40 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 138 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 79 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 280 2 39 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 280 (accept_3_3 77 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 138 280 2 38 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 138 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 75 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 138 280 2 37 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 138 280
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 73 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 138 280 2 36 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 138 280 (accept_3_3 71 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 138 280 2 35 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 138 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 138 280 2 34 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 67 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 280 2 33 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 280 (accept_3_3 65 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 138 280 2 32 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 138 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 138 280 2 31 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 280 2 30 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 280 (accept_3_3 59 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 138 280 2 29 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 138 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 138 280 2 28 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 280
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 55 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 280 2 27 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 280 (accept_3_3 53 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 138 280 2 26 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 138 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 138 280 2 25 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 280 2 24 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 280 (accept_3_3 47 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 138 280 2 23 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 138 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 138 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 138 280 2 22 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 280 2 21 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 280 (accept_3_3 41 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 138 280 2 20 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 138 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 138 280 2 19 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 280
  (Polychromatic418967fa.accept_15_7_3_10_1_817 37 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 280 2 18 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 280 (accept_3_3 35 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 138 280 2 17 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 138 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 280 2 16 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 280 2 15 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 280 (accept_3_3 29 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 280 2 14 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 280 2 13 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 280 2 12 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 280 (accept_3_3 23 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 280 2 11 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 138 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 138 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 280 2 10 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 280
  (Polychromatic418967fa.accept_21_19_12_7_1_15784 19 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 138 280 2 9 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 138 280 (accept_3_3 17 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 138 280 2 8 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 138 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 280 2 7 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 280 2 6 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 280 (accept_3_3 11 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 280 2 5 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 138 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 138 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 280 2 4 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 280 2 3 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 280 (accept_3_3 5 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138
  280 2 2 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  138 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 138 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 138 280 2 1 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 138 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 138 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 137 280 (allA_of_3_1 137 137 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 136 280
  (allA_succ_of_accept 135 136 280 (Polychromatic418967fa.accept_21_9_10_7_1_383 135 136 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 134 136 280 2 67 68 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 136 280
  (Polychromatic418967fa.accept_15_13_1_10_1_816 133 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 132 136 280 4 33 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 131 136 280 (accept_3_3 131 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 136 280 2 65 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 136 280 (Polychromatic418967fa.accept_13_12_6_7_1_1071 129 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 136 280 8 16 17 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 136 280
  (Polychromatic418967fa.accept_15_7_1_10_1_305 127 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 136 280 2 63 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 136 280 (accept_3_3 125 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 136 280 4 31 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 136 280 (Polychromatic418967fa.accept_19_9_3_14_1_2400 123 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 136 280 2 61 68 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 136 280
  (Polychromatic418967fa.accept_13_4_6_7_1_2471 121 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 136 280 8 15 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 136 280 (accept_3_3 119 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 136 280 2 59 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 136 280 (Polychromatic418967fa.accept_23_2_21_4_1_14084 117 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 136 280 4 29 34 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 136 280
  (Polychromatic418967fa.accept_25_15_11_5_1_17200 115 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 136 280 2 57 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 136 280 (accept_3_3 113 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 136 280 8 14 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 136 280 (Polychromatic418967fa.accept_15_6_1_10_1_1549 111 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 136 280 2 55 68 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 136 280
  (Polychromatic418967fa.accept_11_10_4_5_1_359 109 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 136 280 4 27 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 136 280 (accept_3_3 107 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 136 280 2 53 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 136 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 105 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 136 280 8 13 17 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 136 280
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 103 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 136 280 2 51 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 136 280 (accept_3_3 101 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 136 280 4 25 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 136 280 (Polychromatic418967fa.accept_15_9_1_10_1_4316 99 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 136 280 2 49 68 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 136 280
  (Polychromatic418967fa.accept_15_7_1_10_1_305 97 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 136 280 8 12 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 136 280 (accept_3_3 95 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 136 280 2 47 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 136 280 (Polychromatic418967fa.accept_19_17_3_14_1_14557 93 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 136 280 4 23 34 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 136 280
  (Polychromatic418967fa.accept_23_22_21_4_1_17199 91 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 136 280 2 45 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 136 280 (accept_3_3 89 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 136 280 8 11 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 136 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 87 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 136 280 2 43 68 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 136 280
  (Polychromatic418967fa.accept_19_9_3_14_1_2400 85 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 136 280 4 21 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 136 280 (accept_3_3 83 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 136 280 2 41 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 136 280 (Polychromatic418967fa.accept_15_6_1_10_1_1549 81 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 136 280 8 10 17 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 136 280
  (Polychromatic418967fa.accept_13_1_6_7_1_550 79 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 136 280 2 39 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 136 280 (accept_3_3 77 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 136 280 4 19 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 136 280 (Polychromatic418967fa.accept_19_18_3_14_1_5001 75 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 136 280 2 37 68 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 136 280
  (Polychromatic418967fa.accept_15_13_1_10_1_816 73 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 136 280 8 9 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 136 280 (accept_3_3 71 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  136 280 2 35 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 136 280 (Polychromatic418967fa.accept_13_4_6_7_1_2471 69 136 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 136 280 4 17 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 136 280 (Polychromatic418967fa.accept_15_7_1_10_1_305
  67 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 136 280 2 33 68 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 136 280
  (accept_3_3 65 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 136 280 8 8 17 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 136 280
  (Polychromatic418967fa.accept_22_19_4_16_1_6158 63 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 136 280 2 31 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 136 280 (Polychromatic418967fa.accept_13_9_6_7_1_551 61 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 136 280 4 15 34 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 136 280 (accept_3_3 59 136 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 136 280 2 29 68 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 136 280
  (Polychromatic418967fa.accept_21_15_10_7_1_9837 57 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 136 280 8 7 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 136 280 (Polychromatic418967fa.accept_19_17_3_14_1_14557 55 136 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 136 280 2 27 68 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 136 280 (accept_3_3 53
  136 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 136 280 4 13 34 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 136 280
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 51 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 136 280 2 25 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 136 280 (Polychromatic418967fa.accept_19_11_3_14_1_6375 49 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 136 280 8 6 17 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 136 280 (accept_3_3 47 136 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 136 280 2 23 68 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 136 280
  (Polychromatic418967fa.accept_19_7_3_14_1_5023 45 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 136 280 4 11 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 136 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 43 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 136 280 2 21 68 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 136 280 (accept_3_3 41 136 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 136 280 8 5 17 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 136 280
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 39 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 136 280 2 19 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 136 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 136 280 4 9 34 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 136 280 (accept_3_3 35 136 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 136 280 2 17 68 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 136 280
  (Polychromatic418967fa.accept_22_11_4_16_1_15726 33 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 136 280 8 4 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 136 280 (Polychromatic418967fa.accept_22_9_4_16_1_4545 31 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 136 280 2 15 68 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 280 (accept_3_3 29 136 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 280 4 7 34 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 280
  (Polychromatic418967fa.accept_13_1_6_7_1_550 27 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 136 280 2 13 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 136 280 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 136 280 8 3 17 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 136 280 (accept_3_3 23 136 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 136 280 2 11 68 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 136 280
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 136 280 4 5 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 136 280 (Polychromatic418967fa.accept_21_19_10_7_1_8384 19 136 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 136 280 2 9 68 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 136 280 (accept_3_3 17 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 136 280 8 2 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 136 280
  (Polychromatic418967fa.accept_21_15_10_7_1_9837 15 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 136 280 2 7 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 136 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 280 4 3 34 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 280 (accept_3_3 11 136 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 280 2 5 68 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 280
  (Polychromatic418967fa.accept_13_9_6_7_1_551 9 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 280 8 1 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 136 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 280 2 3 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 280 (accept_3_3 5 136 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136 280 4 1 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 136 280 (Polychromatic418967fa.accept_21_3_10_7_1_14215 3 136 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 280 2 1 68 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 280
  (Polychromatic418967fa.accept_13_1_6_7_1_550 1 136 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 136
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 135 280 (allA_succ_of_accept 134 135 280 (accept_3_3 134 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 133 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 133 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 135 280 (Polychromatic418967fa.accept_13_2_5_7_1_1695 132 135
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 135 280 (accept_3_3 131 135
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 135 280 5 26 27 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 135 280
  (Polychromatic418967fa.accept_11_8_3_5_1_355 129 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 135 280 (accept_3_3 128 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 127 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 135 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 126 135 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 125 135 280 5 25 27 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 124 135 280
  (Polychromatic418967fa.accept_16_12_7_8_1_1589 124 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 135 280 (Polychromatic418967fa.accept_18_15_9_10_1_1082 123 135 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 135 280 (accept_3_3 122 135 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 121 135 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 135 280 5 24 27 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 135 280 (accept_3_3
  119 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 135 280
  (Polychromatic418967fa.accept_11_8_3_5_1_355 118 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 135 280 (Polychromatic418967fa.accept_22_7_3_16_1_17198 117 135 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 135 280 (accept_3_3 116 135 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 115 135 280 5 23 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 114 135 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 114 135
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 135 280 (accept_3_3 113 135
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 135 280
  (Polychromatic418967fa.accept_19_17_2_14_1_11897 112 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 135 280 (Polychromatic418967fa.accept_16_15_7_8_1_8189 111 135 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 135 280 5 22 27 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 135 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 109 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 135 280 (Polychromatic418967fa.accept_16_12_7_8_1_1589 108 135 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 135 280 (accept_3_3 107 135 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 135 280 (Polychromatic418967fa.accept_13_2_5_7_1_1695 106 135 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 135 280 5 21 27 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 135 280 (accept_3_3
  104 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 135 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 103 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 135 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 102 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 135 280 (accept_3_3 101 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 135 280 5 20 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 135 280 (Polychromatic418967fa.accept_17_14_16_8_1_3861 99 135 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 135 280 (accept_3_3 98 135 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97
  135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 135 280
  (Polychromatic418967fa.accept_11_8_3_5_1_355 96 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 95 135 280 5 19 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 94 135 280 (Polychromatic418967fa.accept_17_9_16_8_1_2721 94 135 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 135 280
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 93 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 135 280 (accept_3_3 92 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 135 280 5 18 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 135 280 (accept_3_3 89 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 135 280 (Polychromatic418967fa.accept_19_12_2_14_1_10618 88 135 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 135 280
  (Polychromatic418967fa.accept_17_2_16_8_1_3881 87 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 135 280 (accept_3_3 86 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  135 280 5 17 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 135 280 (Polychromatic418967fa.accept_16_4_7_8_1_5753 84 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 280 (accept_3_3 83 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 135 280 (Polychromatic418967fa.accept_17_14_16_8_1_3861 82 135 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 135 280
  (Polychromatic418967fa.accept_16_1_7_8_1_3422 81 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 135 280 5 16 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 135 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 280 (Polychromatic418967fa.accept_12_6_3_4_1_394
  78 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 280 (accept_3_3 77
  135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 280
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 76 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 135 280 5 15 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 135 280 (accept_3_3 74 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 280 (Polychromatic418967fa.accept_25_22_10_5_1_17182 72
  135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 280 (accept_3_3 71
  135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 135 280 5 14 27 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 135 280
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 69 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 135 280 (accept_3_3 68 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 66 135
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 135 280 5 13 27 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 135 280
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 64 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 135 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 280 (accept_3_3 62 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 135 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 280 5 12 27 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 280 (accept_3_3 59 135 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 280 (Polychromatic418967fa.accept_17_7_16_8_1_7613 58 135
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 280
  (Polychromatic418967fa.accept_16_9_7_8_1_1588 57 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 135 280 (accept_3_3 56 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  135 280 5 11 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 135 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 280 (accept_3_3 53 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 135 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 52 135 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 280
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 51 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 135 280 5 10 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 135 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 280
  (Polychromatic418967fa.accept_17_14_16_8_1_3861 48 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 280 (accept_3_3 47 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 280 (Polychromatic418967fa.accept_19_8_2_14_1_3640 46 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 280 5 9 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 280 (accept_3_3 44 135 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 135 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 135 280 (accept_3_3 41 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  135 280 5 8 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 135 280 (Polychromatic418967fa.accept_19_1_2_14_1_3666 39 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 280 (accept_3_3 38 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 280 (Polychromatic418967fa.accept_16_4_7_8_1_5753 36 135
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 135 280 5 7 27 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 135 280
  (Polychromatic418967fa.accept_21_13_9_7_1_9858 34 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 135 280 (Polychromatic418967fa.accept_16_1_7_8_1_3422 33 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 280 (accept_3_3 32 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 135 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 280 5 6 27 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 280 (accept_3_3 29 135 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 280 (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 135
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 280
  (Polychromatic418967fa.accept_19_8_2_14_1_3640 27 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 280 (accept_3_3 26 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  135 280 5 5 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 135 280 (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 280 (accept_3_3 23 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 280 (Polychromatic418967fa.accept_25_22_10_5_1_17182 22 135 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 280
  (Polychromatic418967fa.accept_24_21_15_16_1_17197 21 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 135 280 5 4 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 280 (accept_3_3 17 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 280 (Polychromatic418967fa.accept_19_16_2_14_1_9221 16 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 135 280 5 3 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 135 280 (accept_3_3 14 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 135 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 280 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 135
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 280 (accept_3_3 11 135
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 135 280 5 2 27 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 135 280
  (Polychromatic418967fa.accept_16_9_7_8_1_1588 9 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 280 (accept_3_3 8 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 135 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 135 280 5 1 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 280 (Polychromatic418967fa.accept_16_4_7_8_1_5753 4
  135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 280
  (Polychromatic418967fa.accept_21_3_9_7_1_8369 3 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 280 (accept_3_3 2 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 135 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 134 280 (allA_of_3_1 134 134 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 133 280
  (allA_succ_of_accept 132 133 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 132 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 133 280 (accept_3_3 131 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 130 133 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 130 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 133 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 129 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 133 280 (accept_3_3 128 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 133 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 127 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 133 280 7 18 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 133 280 (accept_3_3 125 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 133 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 124 133 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 133 280 (Polychromatic418967fa.accept_6_3_1_4_1_25
  123 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 133 280 (accept_3_3
  122 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 133 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 121 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 133 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 120 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 119 133 280 7 17 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 118 133 280 (Polychromatic418967fa.accept_12_10_1_4_1_392
  118 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 133 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 133 280 (accept_3_3 116 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 133 280 (Polychromatic418967fa.accept_13_11_3_7_1_2513 115 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 133 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 114 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 133 280 (accept_3_3 113 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 133 280 7 16 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 133 280 (Polychromatic418967fa.accept_6_3_1_4_1_25
  111 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 133 280 (accept_3_3
  110 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 133 280
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 109 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 133 280 (Polychromatic418967fa.accept_13_4_3_7_1_2515 108 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 133 280 (accept_3_3 107 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 133 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 106 133
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 133 280 7 15 19 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 133 280 (accept_3_3
  104 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 133 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 103 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 133 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 102 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 133 280 (accept_3_3 101 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 133 280 (Polychromatic418967fa.accept_13_9_3_7_1_1065 100 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 133 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 133 280 7 14 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 133 280 (Polychromatic418967fa.accept_25_22_8_5_1_17196 97 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 133 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 96 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 133 280 (accept_3_3 95 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 133 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 94 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 133 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 133 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 133 280 (accept_3_3 92 133 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 91 133 280 7 13 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 133 280 (Polychromatic418967fa.accept_26_12_3_20_1_15486 90 133
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 280 (accept_3_3 89 133
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 280
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 88 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 133 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 133 280 (accept_3_3 86 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 133 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 133 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 133 280 7 12 19 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 133 280 (accept_3_3 83 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 133 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 133
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 133 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 133 280 (accept_3_3 80 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 133 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 79 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 133 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 78 133 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 133 280 7 11 19 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 133 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 76 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 133 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 133 280 (accept_3_3 74 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 133 280 (Polychromatic418967fa.accept_13_8_3_7_1_2455 73 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 133 280
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 133 280 (accept_3_3 71 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  133 280 7 10 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 133 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 133 280 (accept_3_3 68 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 133 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 133 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 133 280 (Polychromatic418967fa.accept_9_3_7_1_1_143
  66 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 280 (accept_3_3 65
  133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 280
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 64 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 133 280 7 9 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 133 280 (accept_3_3 62 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 133 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 61 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 133 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 280 (accept_3_3 59 133 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 280 (Polychromatic418967fa.accept_9_4_7_1_1_379
  58 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 133 280 7 8 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 133 280 (Polychromatic418967fa.accept_23_9_18_4_1_17195 55 133 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 280
  (Polychromatic418967fa.accept_23_8_18_4_1_12472 54 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 133 280 (accept_3_3 53 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 133 280 (Polychromatic418967fa.accept_16_4_5_8_1_2425 52 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 133 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 280 (accept_3_3 50 133 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 133 280 7 7 19 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 133 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 133 280 (accept_3_3 47 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 133 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 133 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 133 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 280 (accept_3_3 44 133 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 280 (Polychromatic418967fa.accept_13_4_3_7_1_2515 43 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 133 280 7 6 19 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 133 280 (accept_3_3 41 133 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 280 (Polychromatic418967fa.accept_9_4_7_1_1_379
  40 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 280 (accept_3_3 38 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 280 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 280 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 133 280 7 5 19 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 133 280
  (Polychromatic418967fa.accept_12_10_1_4_1_392 34 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 133 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 280 (accept_3_3 32 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 133 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 133 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 280 (Polychromatic418967fa.accept_9_3_7_1_1_143
  30 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 280 (accept_3_3 29
  133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 133 280 7 4 19 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 133 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 280 (accept_3_3 26 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 280 (Polychromatic418967fa.accept_23_2_18_4_1_9145 25 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 133 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 280 (accept_3_3 23 133 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 133 280 7 3 19 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 133 280 (accept_3_3 20 133 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 280
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 280 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 280 (accept_3_3 17 133 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 133
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 133 280 7 2 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 133 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 133 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 280 (accept_3_3 11 133 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 280 (Polychromatic418967fa.accept_12_10_1_4_1_392
  10 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 280 (accept_3_3 8 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 133
  280 7 1 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  133 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 133 280 (accept_3_3 5 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 133 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 133 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 133 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 280 (accept_3_3 2 133 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710
  1 133 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 132 280 (allA_succ_of_accept 131 132 280 (accept_3_3 131 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 132 280 2 65 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 132 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 129 132 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 132 280 4 32 33 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 132 280
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 127 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 132 280 2 63 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 132 280 (accept_3_3 125 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 132 280 4 31 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 132 280 (Polychromatic418967fa.accept_16_11_4_8_1_3435 123 132 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 132 280 2 61 66 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 132 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 121 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 132 280 4 30 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 132 280 (accept_3_3 119 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 132 280 2 59 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 132 280 (Polychromatic418967fa.accept_16_5_4_8_1_1560 117 132 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 132 280 4 29 33 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 132 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 115 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 132 280 2 57 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 132 280 (accept_3_3 113 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 132 280 4 28 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 132 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 111 132 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 132 280 2 55 66 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 132 280
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 109 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 132 280 4 27 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 132 280 (accept_3_3 107 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 132 280 2 53 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 132 280 (Polychromatic418967fa.accept_16_9_4_8_1_2533 105 132 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 132 280 4 26 33 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 132 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 103 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 132 280 2 51 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 132 280 (accept_3_3 101 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 132 280 4 25 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 132 280 (Polychromatic418967fa.accept_13_8_2_7_1_2452 99 132 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 132 280 2 49 66 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 97 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 132 280 4 24 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 132 280 (accept_3_3 95 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 132 280 2 47 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 132 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 132 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 132 280 4 23 33 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 280
  (Polychromatic418967fa.accept_16_11_4_8_1_3435 91 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 132 280 2 45 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 132 280 (accept_3_3 89 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 132 280 4 22 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 132 280 (Polychromatic418967fa.accept_13_9_2_7_1_1083 87 132 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 132 280 2 43 66 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 132 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 85 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 280 4 21 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 280 (accept_3_3 83 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 132 280 2 41 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 132 280 (Polychromatic418967fa.accept_15_6_12_10_1_1543 81 132 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 132 280 4 20 33 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 132 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 79 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 280 2 39 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 280 (accept_3_3 77 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 132 280 4 19 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 132 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 132 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 132 280 2 37 66 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 132 280
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 73 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 280 4 18 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 280 (accept_3_3 71 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 132 280 2 35 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 132 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 69 132 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 132 280 4 17 33 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 67 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 280 2 33 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 280 (accept_3_3 65 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 132 280 4 16 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 132 280 (Polychromatic418967fa.accept_16_15_4_8_1_1562 63 132 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 132 280 2 31 66 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 61 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 280 4 15 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 280 (accept_3_3 59 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 132 280 2 29 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 132 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 132 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 132 280 4 14 33 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 132 280
  (Polychromatic418967fa.accept_16_7_4_8_1_2487 55 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 280 2 27 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 280 (accept_3_3 53 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 132 280 4 13 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 132 280 (Polychromatic418967fa.accept_15_6_12_10_1_1543 51 132 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 132 280 2 25 66 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 280 4 12 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 280 (accept_3_3 47 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 280 2 23 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 132 280 (Polychromatic418967fa.accept_16_13_4_8_1_4557 45 132 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 280 4 11 33 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 280 2 21 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 280 (accept_3_3 41 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 132 280 4 10 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 132 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 132 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 132 280 2 19 66 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 280
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 37 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 132 280 4 9 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 132 280 (accept_3_3 35 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 132 280 2 17 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 132 280 (Polychromatic418967fa.accept_16_1_4_8_1_3434 33 132 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 280 4 8 33 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 280 2 15 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 280 (accept_3_3 29 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 280 4 7 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 132 280 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 132 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 280 2 13 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 25
  132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 280 4 6 33 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 280 (accept_3_3 23
  132 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 280 2 11 66 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 280 4 5 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 132 280 (Polychromatic418967fa.accept_16_3_4_8_1_3450 19 132 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 280 2 9 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 280 (accept_3_3 17 132 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 280 4 4 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 280 (Polychromatic418967fa.accept_16_15_4_8_1_1562 15 132
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 280 2 7 66 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 280 4 3 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 280 (accept_3_3 11 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  132 280 2 5 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 132 280 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 132 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 280 4 2 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 132 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 280 2 3 66 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 280 (accept_3_3 5
  132 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 280 4 1 33 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 132 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 132 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 132 280 2 1 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 132 280 (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 132 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 131 280 (allA_of_3_1 131 131 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 130 280
  (allA_succ_of_accept 129 130 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 129 130 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 130 280 2 64 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 130 280 (Polychromatic418967fa.accept_12_7_10_4_1_382
  127 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 130 280 2 63 65 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 125 130 280 5 25 26
  56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 124 130 280 2 62
  65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 130
  280 (Polychromatic418967fa.accept_9_6_4_1_1_390 123 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 122 130 280 2 61 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 121 130 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 121 130 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 130 280 10 12 13 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 130 280 (accept_3_3
  119 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 130 280 2 59 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 130 280
  (Polychromatic418967fa.accept_11_7_9_5_1_338 117 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 130 280 2 58 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 115 130 280 5 23 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 114 130 280 2 57 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 130 280 (accept_3_3 113 130 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 112 130 280 2 56 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 111 130 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 111 130 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 130 280 10 11 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 130 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 109 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 130 280 2 54 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 130 280 (accept_3_3 107 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 130 280 2 53 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 130 280 5 21 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 130 280 2 52 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 130 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 103 130
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 130 280 2 51 65 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 130 280 (accept_3_3
  101 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 130 280 10 10 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 130 280
  (Polychromatic418967fa.accept_17_14_11_8_1_3854 99 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 130 280 2 49 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 130 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 97 130 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 130 280 2 48 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 130 280 5 19 26 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 130 280 2 47 65 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 130 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 93 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 130 280 2 46 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 130 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 91 130 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 130 280 10 9 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 130 280 (accept_3_3 89 130 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 130 280 2 44 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 130 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 87 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 130 280 2 43 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 130 280 5 17 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 130 280 2 42 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 130 280 (accept_3_3 83 130 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 130 280 2 41 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 130 280 (Polychromatic418967fa.accept_19_5_16_14_1_2374 81 130 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 130 280 10 8 13 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 130 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 79 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 130 280 2 39 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 130 280 (accept_3_3 77 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 130 280 2 38 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 130 280 5 15 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 130 280 2 37 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 130 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 73 130 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 130 280 2 36 65 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 130 280 (accept_3_3 71
  130 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 130 280 10 7 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 130 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 69 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 130 280 2 34 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 130 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 67 130 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 130 280 2 33 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 130 280 5 13 26 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 130 280 2 32 65 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 130 280
  (Polychromatic418967fa.accept_24_15_10_16_1_10574 63 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 130 280 2 31 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 130 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 130 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 130 280 10 6 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 130 280 (accept_3_3 59 130 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 130 280 2 29 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 130 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 130 280 2 28 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 130 280 5 11 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 130 280 2 27 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 130 280 (accept_3_3 53 130 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 130 280 2 26 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 130 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 130 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 280 10 5 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 130 280 2 24 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 130 280 (accept_3_3 47 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 280 2 23 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 130 280 5 9 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 130 280 2 22 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 130 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 130 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 130 280 2 21 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 130 280 (accept_3_3 41 130 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 130 280 10 4 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 130 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 130 280 2 19 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 130 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 130 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 130 280 2 18 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 130 280 5 7 26 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 130 280 2 17 65 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 130 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 130 280 2 16 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 130 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 130 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 130 280 10 3 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 130 280 (accept_3_3 29 130 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 130 280 2 14 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 130 280
  (Polychromatic418967fa.accept_21_6_4_7_1_3734 27 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 130 280 2 13 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 130 280 5 5 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 130 280 2 12 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 130 280 (accept_3_3 23 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 280 2 11 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 130 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 280 10 2 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 280 2 9 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 130 280 (accept_3_3 17 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 130 280 2 8 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 130 280 5 3 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 130 280 2 7 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 130 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 280 2 6 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 280 (accept_3_3 11 130 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 280 10 1 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 280
  (Polychromatic418967fa.accept_17_9_11_8_1_5077 9 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 280 2 4 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 130 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 280 2 3 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 130 280 5 1 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 130 280 2 2 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 130 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3
  130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 280 2 1 65 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 130 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 130
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 129 280 (allA_succ_of_accept 128 129 280 (accept_3_3 128 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 127 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 129 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 126 129
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 129 280 (accept_3_3 125 129
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 129 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 124 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 129 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 123 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 129 280 (accept_3_3 122 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 121 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 121 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 129 280
  (Polychromatic418967fa.accept_21_15_3_7_1_6748 120 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 129 280 (accept_3_3 119 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 129 280 (Polychromatic418967fa.accept_19_4_15_14_1_10614 118 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 129 280
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 117 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 129 280 (accept_3_3 116 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 129 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 114 129
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 129 280 (accept_3_3 113 129
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 129 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 112 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 129 280 (Polychromatic418967fa.accept_16_15_1_8_1_1585 111 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 129 280 (accept_3_3 110 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 109 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 129 280
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 108 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 129 280 (accept_3_3 107 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 129 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 106 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 129 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 105 129
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 129 280 (accept_3_3 104 129
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 103 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 129 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 102 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 129 280 (accept_3_3 101 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 129 280 (Polychromatic418967fa.accept_16_4_1_8_1_835 100 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 129 280
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 99 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 129 280 (accept_3_3 98 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 129 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 96 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 129 280 (accept_3_3 95 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 129 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 94 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 129 280
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 93 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 129 280 (accept_3_3 92 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 129 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 90 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 280 (accept_3_3 89 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 88 129 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 87 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 129 280 (accept_3_3 86 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 129 280 (Polychromatic418967fa.accept_13_6_12_7_1_5131 84 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 280 (accept_3_3 83 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 280 (Polychromatic418967fa.accept_13_4_12_7_1_2439 82 129
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 280
  (Polychromatic418967fa.accept_22_15_19_16_1_14130 81 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 129 280 (accept_3_3 80 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 78 129 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 280 (accept_3_3 77 129 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 280 (Polychromatic418967fa.accept_9_4_3_1_1_154
  76 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 280
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 75 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 129 280 (accept_3_3 74 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 280 (Polychromatic418967fa.accept_15_12_9_10_1_2326 72 129
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 280 (accept_3_3 71 129
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 70 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 129 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 280 (accept_3_3 68 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 280 (Polychromatic418967fa.accept_12_6_9_4_1_96
  66 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 280 (accept_3_3 65
  129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 280
  (Polychromatic418967fa.accept_15_4_9_10_1_5384 64 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 129 280 (Polychromatic418967fa.accept_13_11_12_7_1_2443 63 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 280 (accept_3_3 62 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 129 280 (accept_3_3 59 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 129 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 129 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 280 (accept_3_3 56 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 129 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 129 280 (accept_3_3 53 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 129 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 129 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 280 (accept_3_3 50 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 280
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 48 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 129 280 (accept_3_3 47 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 129 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 46 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 129 280 (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 280 (accept_3_3 44 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 129 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 129 280 (accept_3_3 41 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 129 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 129 280 (Polychromatic418967fa.accept_16_7_1_8_1_5796 39 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 280 (accept_3_3 38 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 129 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 36 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 129 280 (accept_3_3 35 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 129 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 129 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 280 (accept_3_3 32 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 129 280 (accept_3_3 29 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 129 280 (Polychromatic418967fa.accept_16_12_1_8_1_5767 28 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 129 280 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 280 (accept_3_3 26 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 280 (accept_3_3 23 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 129 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 280 (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 280 (accept_3_3 20 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 129 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 129 280 (accept_3_3 17 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 129 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 129 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 280 (accept_3_3 14 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 280
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 280 (accept_3_3 11 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 280 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 280 (Polychromatic418967fa.accept_16_9_1_8_1_5766
  9 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 280 (accept_3_3 8
  129 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 129 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 280 (accept_3_3 5 129 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 129 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 129 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 3
  129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 280 (accept_3_3 2 129
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 129 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 128 280 (allA_of_3_1 128 128 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 127 280
  (allA_succ_of_accept 126 127 280 (Polychromatic418967fa.accept_19_12_13_14_1_9198 126 127 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 127 280 (accept_3_3 125 127 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 124 127 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 124 127 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 123 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 127 280 (accept_3_3 122 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 127 280 (Polychromatic418967fa.accept_13_4_10_7_1_1701 121 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 120 127 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 120 127 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 127 280 (accept_3_3 119 127 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 127 280
  (Polychromatic418967fa.accept_12_10_7_4_1_820 118 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 127 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 117 127 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 127 280 (accept_3_3 116 127 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 127 280 (Polychromatic418967fa.accept_19_1_13_14_1_3509 115 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 127 280
  (Polychromatic418967fa.accept_24_18_7_16_1_15629 114 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 127 280 (accept_3_3 113 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 127 280 (Polychromatic418967fa.accept_13_8_10_7_1_1702 112 127 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 127 280 (Polychromatic418967fa.accept_6_3_1_4_1_25
  111 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 127 280 (accept_3_3
  110 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 127 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 109 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 127 280 (Polychromatic418967fa.accept_13_4_10_7_1_1701 108 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 127 280 (accept_3_3 107 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 127 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 106 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 127 280 (accept_3_3 104 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 127 280 (Polychromatic418967fa.accept_13_12_10_7_1_2433 103 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 127 280 (Polychromatic418967fa.accept_15_12_7_10_1_3297 102 127 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 127 280 (accept_3_3 101 127 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 127 280
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 100 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 127 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 127 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 127 280 (accept_3_3 98 127 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 127 280 (Polychromatic418967fa.accept_16_1_15_8_1_2411 97 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 127 280
  (Polychromatic418967fa.accept_19_1_13_14_1_3509 96 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 127 280 (accept_3_3 95 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 127 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 94 127 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 127 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 127 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 127 280 (accept_3_3 92 127 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 127 280 (Polychromatic418967fa.accept_15_1_7_10_1_287
  91 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 127 280
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 90 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 127 280 (accept_3_3 89 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 127 280 (Polychromatic418967fa.accept_18_16_1_10_1_2029 88 127 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 127 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87
  127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 127 280 (accept_3_3 86
  127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 127 280
  (Polychromatic418967fa.accept_18_13_1_10_1_4331 85 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 127 280 (Polychromatic418967fa.accept_16_4_15_8_1_2413 84 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 280 (accept_3_3 83 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 82 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 127 280 (accept_3_3 80 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 127 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 79 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 127 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 78 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 280 (accept_3_3 77 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 76 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 280 (accept_3_3 74 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 280 (Polychromatic418967fa.accept_13_8_10_7_1_1702 73 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 127 280 (Polychromatic418967fa.accept_15_12_7_10_1_3297 72 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 280 (accept_3_3 71 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 280 (accept_3_3 68 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 67 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 280 (Polychromatic418967fa.accept_21_3_1_7_1_5187 66 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 280 (accept_3_3 65 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 280 (Polychromatic418967fa.accept_13_12_10_7_1_2433 64 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 280 (accept_3_3 62 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 61 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 280 (Polychromatic418967fa.accept_13_8_10_7_1_1702 60 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 280 (accept_3_3 59 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 280 (accept_3_3 56 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 55 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 127 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 280 (accept_3_3 53 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 280 (Polychromatic418967fa.accept_16_4_15_8_1_2413 52 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 280 (accept_3_3 50 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 49 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 280 (Polychromatic418967fa.accept_15_3_7_10_1_2324 48 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 280 (accept_3_3 47 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 280 (accept_3_3 44 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 42 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 280 (accept_3_3 41 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 280 (Polychromatic418967fa.accept_21_19_1_7_1_3724 40 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 280 (accept_3_3 38 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 280 (Polychromatic418967fa.accept_19_18_13_14_1_4995 37 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 280 (Polychromatic418967fa.accept_16_4_15_8_1_2413 36 127 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 280 (accept_3_3 35 127 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732
  34 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 280 (accept_3_3 32 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 280 (Polychromatic418967fa.accept_13_4_10_7_1_1701 30 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 280 (accept_3_3 29 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 280 (Polychromatic418967fa.accept_16_12_15_8_1_4586 28 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 280 (accept_3_3 26 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 280 (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 280 (Polychromatic418967fa.accept_19_5_13_14_1_6366 24 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 280 (accept_3_3 23 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 280 (accept_3_3 20 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 280 (Polychromatic418967fa.accept_15_3_7_10_1_2324 18 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 280 (accept_3_3 17 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 16 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 280 (accept_3_3 14 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 280 (Polychromatic418967fa.accept_18_13_1_10_1_4331 13 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 280 (accept_3_3 11 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 280 (accept_3_3 8 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 280 (Polychromatic418967fa.accept_16_7_15_8_1_278 7 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 280 (Polychromatic418967fa.accept_21_6_1_7_1_11405 6 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 280 (accept_3_3 5 127 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 280 (Polychromatic418967fa.accept_13_4_10_7_1_1701 4 127
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 280 (accept_3_3 2 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 127 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 126 280 (allA_succ_of_accept 125 126 280 (accept_3_3 125 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 126 280 2 62 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 126 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 123 126 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 126 280 2 61 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 126 280
  (Polychromatic418967fa.accept_13_4_9_7_1_2402 121 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 126 280 2 60 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 119 126 280 7 17 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 118 126 280 2 59 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 126 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 117 126
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 126 280 2 58 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 126 280
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 115 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 126 280 2 57 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 126 280 (accept_3_3 113 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 126 280 14 8 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 126 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 111 126 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 126 280 2 55 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 126 280
  (Polychromatic418967fa.accept_15_4_6_10_1_823 109 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 126 280 2 54 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 126 280 (accept_3_3 107 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 126 280 2 53 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 126 280 7 15 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 126 280 2 52 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 126 280 (Polychromatic418967fa.accept_17_1_7_8_1_6347 103 126
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 126 280 2 51 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 126 280 (accept_3_3
  101 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 126 280 2 50 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 126 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 99 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 126 280 14 7 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 97 126 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430 97 126 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 126 280 2 48 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 126 280 (accept_3_3 95 126 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 94 126 280 2 47 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 126 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 93 126 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 126 280 2 46 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 91 126 280 7 13 18 40
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 90 126 280 2 45 63
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 126 280
  (accept_3_3 89 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 280 2 44 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 126 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 87 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 126 280 2 43 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 126 280 (Polychromatic418967fa.accept_19_9_12_14_1_4966 85 126 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 126 280 14 6 9 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 126 280 (accept_3_3 83 126 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 280 2 41 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 81 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 126 280 2 40 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 126 280 (Polychromatic418967fa.accept_15_4_6_10_1_823 79 126 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 126 280 2 39 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 126 280 7 11 18 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 126 280 2 38 63 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 126 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 75 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 126 280 2 37 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 126 280 (Polychromatic418967fa.accept_13_8_9_7_1_530 73 126 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 126 280 2 36 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 126 280 (accept_3_3 71 126 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 280 14 5 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 126 280 (Polychromatic418967fa.accept_12_9_6_4_1_402
  69 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 126 280 2 34 63 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 280
  (Polychromatic418967fa.accept_13_2_9_7_1_164 67 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 280 2 33 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 280 (accept_3_3 65 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 126 280 2 32 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 126 280 7 9 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 62 126 280 2 31 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 126 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 61 126 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 126 280 2 30 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 126 280 (accept_3_3 59 126 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 280 2 29 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 126 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 57 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 126 280 14 4 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 126 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 55 126 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 126 280 2 27 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 126 280 (accept_3_3 53 126 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 280 2 26 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 126 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 126 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 126 280 2 25 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 126 280 7 7 18 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 126 280 2 24 63 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 126 280
  (accept_3_3 47 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 280 2 23 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 280 2 22 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 43 126 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 280 14 3 9 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 280 (accept_3_3 41 126 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 280 2 20 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 39 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 280 2 19 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 280 (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 126 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 126 280 2 18 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 126 280 7 5 18 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 126 280 2 17 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 280 2 16 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 31 126 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 280 2 15 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 280 (accept_3_3 29 126 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 280 14 2 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 280 (Polychromatic418967fa.accept_12_3_6_4_1_400
  27 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 126 280 2 13 63 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 280
  (Polychromatic418967fa.accept_19_6_12_14_1_17194 25 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 126 280 2 12 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 126 280 (accept_3_3 23 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 280 2 11 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 126 280 7 3 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 126 280 2 10 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 126 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 126 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 280 2 9 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 280 (accept_3_3 17 126 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 280 2 8 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 15 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 280 14 1 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 126 280 (Polychromatic418967fa.accept_19_13_12_14_1_9217 13 126 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 280 2 6 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 280 (accept_3_3 11 126 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 280 2 5 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9
  126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 280 2 4 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 126 280 7 1 18 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 126 280 2 3 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 280 (accept_3_3 5
  126 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 280 2 2 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 126 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 3 126 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 126 280 2 1 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 126 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 1 126 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 126
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 125 280 (allA_of_3_1 125 125 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 124 280
  (allA_succ_of_accept 123 124 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 123 124 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 124 280 2 61 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 124 280 (Polychromatic418967fa.accept_9_4_7_1_1_379
  121 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 124 280 4 30 31 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 124 280
  (accept_3_3 119 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 124 280 2 59 62 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 124 280
  (Polychromatic418967fa.accept_16_5_12_8_1_2521 117 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 124 280 4 29 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 124 280 (Polychromatic418967fa.accept_16_3_12_8_1_808 115 124 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 124 280 2 57 62 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 124 280 (accept_3_3
  113 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 124 280 4 28 31 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 124 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 111 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 124 280 2 55 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 124 280 (Polychromatic418967fa.accept_16_13_12_8_1_2451 109 124 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 124 280 4 27 31 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 124 280 (accept_3_3 107 124 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 124 280 2 53 62 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 124 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 105 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 124 280 4 26 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 124 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 103 124 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 124 280 2 51 62 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 124 280 (accept_3_3 101 124 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 124 280 4 25 31 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 124 280
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 99 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 124 280 2 49 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 124 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 97 124 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 124 280 4 24 31 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 124 280 (accept_3_3 95 124 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 124 280 2 47 62 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 124 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 93 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 124 280 4 23 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 124 280 (Polychromatic418967fa.accept_16_11_12_8_1_1592 91 124 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 124 280 2 45 62 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 124 280 (accept_3_3 89 124 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 124 280 4 22 31 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 124 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 87 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 124 280 2 43 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 124 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 124 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 124 280 4 21 31 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 124 280 (accept_3_3 83 124 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 124 280 2 41 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 124 280 (Polychromatic418967fa.accept_15_6_4_10_1_2319
  81 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 124 280 4 20 31 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 124 280
  (Polychromatic418967fa.accept_16_15_12_8_1_4585 79 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 124 280 2 39 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 124 280 (accept_3_3 77 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 124 280 4 19 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 124 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 124 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 124 280 2 37 62 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 124 280
  (Polychromatic418967fa.accept_15_13_4_10_1_821 73 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 124 280 4 18 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 280 (accept_3_3 71 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 280 2 35 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 124 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 280 4 17 31 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 67 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 280 2 33 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 280 (accept_3_3 65 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 280 4 16 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 124 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 280 2 31 62 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 280
  (Polychromatic418967fa.accept_16_13_12_8_1_2451 61 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 124 280 4 15 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 124 280 (accept_3_3 59 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 280 2 29 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 124 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 280 4 14 31 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 280
  (Polychromatic418967fa.accept_16_7_12_8_1_2450 55 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 280 2 27 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 280 (accept_3_3 53 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 280 4 13 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 124 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 280 2 25 62 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 280 4 12 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 280 (accept_3_3 47 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 280 2 23 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 280 (Polychromatic418967fa.accept_16_13_12_8_1_2451 45 124 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 280 4 11 31 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 280
  (Polychromatic418967fa.accept_15_13_4_10_1_821 43 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 280 2 21 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 280 (accept_3_3 41 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 280 4 10 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 124 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 280 2 19 62 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 280
  (Polychromatic418967fa.accept_15_7_4_10_1_1513 37 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 280 4 9 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 124 280 (accept_3_3 35 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  124 280 2 17 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 124 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 124 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 280 4 8 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31
  124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 124 280 2 15 62 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 280 (accept_3_3 29
  124 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 280 4 7 31 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 280
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 124 280 2 13 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 124 280 (Polychromatic418967fa.accept_16_9_12_8_1_1554 25 124 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 280 4 6 31 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 280 (accept_3_3 23 124 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 280 2 11 62 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 124 280 4 5 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 124 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 124 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 280 2 9 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 280 (accept_3_3 17 124 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 280 4 4 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 124 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 280 2 7 62 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 280 4 3 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 124 280 (accept_3_3 11 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  124 280 2 5 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 124 280 (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 124 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 280 4 2 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 124 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 280 2 3 62 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 280 (accept_3_3 5
  124 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 280 4 1 31 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 124 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 124 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 124 280 2 1 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 124 280 (Polychromatic418967fa.accept_16_1_12_8_1_2405 1 124 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 124
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_280_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


